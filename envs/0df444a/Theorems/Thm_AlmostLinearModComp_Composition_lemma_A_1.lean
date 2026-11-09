-- Prove2me | Theorems.Thm_AlmostLinearModComp_Composition_lemma_A_1
-- name    : AlmostLinearModComp.Composition.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:17.160264+00:00
-- url     : https://prove2.me/theorems/657484ea-0ec3-4805-9e58-2b6d190264d6
-- title:
--   Lemma A.1 — Fast arithmetic
-- statement:
--   Let $R$ be any commutative ring with identity. There are absolute $C>0$ and $k\in\mathbb N$, independent of $R$ and $s$, such that for each integer $s\ge1$:
--
--   1. A bilinear integer-scalar program computes every coefficient of the product of two degree-below-$s$ polynomials.
--   2. A division-free circuit, given the first $s$ coefficients of any polynomial $u$ with $u(0)=1$, computes the unique truncated reciprocal $h$ satisfying $uh\equiv1\pmod{X^s}$.
--   3. For a monic degree-$s$ polynomial $F$, a division-free preprocessing circuit computes a scalar table from its lower coefficients. A linear program using exactly that table computes every coefficient of $h\operatorname{rem}F$ for every $\deg h<2s$.
--
--   Each total operation bound is
--   $$Cs(1+\log_2(s+2))^k,$$
--   including the preprocessing in the third assertion. With either multiplication factor fixed, the variable factor is processed by a linear program using the integer table and the explicitly transformed fixed factor, within the multiplication bound. All programs are chosen independently of the ring and coefficient inputs.
--
--   This packages the arithmetic and linearity interfaces needed by the coordinate-change construction; none is assumed as an axiom. All three arithmetic clauses and the bilinear and fixed-factor clauses are conclusions of this single open item.
--
--   Differences from the source:
--   - encoding: coefficient vectors and soft-O(s) operations → finite output lists and C s (1+log₂(s+2))^k with absolute C,k; reason: the standard soft-O quantifiers are explicit, and the multiplication output includes one trailing zero coefficient in a list of length 2s
--   - encoding: linear computation with one factor fixed and remainder after preprocessing → a separate scalar table and valid linear programs, with actual preprocessing circuits; reason: this exposes dependence on fixed data without changing the allowed ring inputs
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), Lemma A.1 and its following bilinearity paragraph, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Bilinear

namespace AlmostLinearModComp.Composition

/-- Zhou--Wang, Lemma A.1, printed p.11 / PDF p.12, all clauses.
Preprocessing is a division-free circuit, not a supplied inverse or scalar oracle. -/
theorem lemma_A_1 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ s : ℕ, 1 ≤ s →
      ∃ (b : BilinearProgram) (inverse prepare : Circuit) (remainder : LinearProgram)
        (fixedLeft fixedRight : LinearProgram),
        b.valid s (2 * s) ∧
        inverse.valid s s ∧
        prepare.valid s (prepare.outputs.length) ∧
        remainder.valid prepare.outputs.length (2 * s) s ∧
        fixedLeft.valid (b.scalars.length + b.rank) s (2 * s) ∧
        fixedRight.valid (b.scalars.length + b.rank) s (2 * s) ∧
        (b.cost : ℝ) ≤ arithmeticBound C k s ∧
        (inverse.cost : ℝ) ≤ arithmeticBound C k s ∧
        ((prepare.cost + remainder.cost : ℕ) : ℝ) ≤ arithmeticBound C k s ∧
        fixedLeft.cost ≤ b.cost ∧ fixedRight.cost ≤ b.cost ∧
        ∀ (R : Type) [CommRing R],
          (∀ p q : Polynomial R,
            p.degree < (s : WithBot ℕ) → q.degree < (s : WithBot ℕ) →
            b.eval (List.ofFn fun i : Fin s => p.coeff i)
                (List.ofFn fun i : Fin s => q.coeff i) =
              List.ofFn (fun i : Fin (2 * s) => (p * q).coeff i)) ∧
          (∀ u : Polynomial R, u.coeff 0 = 1 →
            ∃ h : Polynomial R, h.degree < (s : WithBot ℕ) ∧
              inverse.eval (List.ofFn fun i : Fin s => u.coeff i) =
                List.ofFn (fun i : Fin s => h.coeff i) ∧
              ∀ i < s, (u * h).coeff i = if i = 0 then 1 else 0) ∧
          (∀ F h : Polynomial R, F.Monic → F.degree = (s : WithBot ℕ) →
            h.degree < ((2 * s : ℕ) : WithBot ℕ) →
            remainder.eval
                (prepare.eval (List.ofFn fun i : Fin s => F.coeff i))
                (List.ofFn fun i : Fin (2 * s) => h.coeff i) =
              List.ofFn (fun i : Fin s => (h %ₘ F).coeff i)) ∧
          (∀ x y : List R, x.length = s → y.length = s →
            let scalars := b.scalars.map (fun z : ℤ => (z : R))
            fixedLeft.eval (scalars ++ b.left.eval scalars x) y = b.eval x y ∧
            fixedRight.eval (scalars ++ b.right.eval scalars y) x = b.eval x y) := by sorry

end AlmostLinearModComp.Composition
