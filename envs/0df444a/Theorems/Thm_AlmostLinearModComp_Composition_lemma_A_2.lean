-- Prove2me | Theorems.Thm_AlmostLinearModComp_Composition_lemma_A_2
-- name    : AlmostLinearModComp.Composition.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:16.976402+00:00
-- url     : https://prove2.me/theorems/b6dba215-fb9d-4ede-9acd-5f2f4293a5ff
-- title:
--   Lemma A.2 — Transposition principle
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let a valid linear program with $c$ gates compute $Ax$ for an $r\times s$ matrix $A$ over any commutative ring $R$, using a fixed list of $k$ scalars. The explicit reverse-accumulation compiler produces a valid linear program computing every entry of $A^{\mathsf T}b$ for every $b\in R^r$, with
--   $$\operatorname{cost}\le C(c+r+s).$$
--   It uses the same scalar list and constructs its instructions from the original program alone; the matrix is never supplied to the compiler. The cost of preparing the fixed scalars is separate.
--
--   For every $q\ge1$, if the original program computes the $R$-linear coefficient map of a matrix over $R[t]/(t^q)$, reversing each coefficient block before and after transposition computes the coefficient map of $A^{\mathsf T}$ in
--   $$C\bigl(c+(r+s)q\bigr)$$
--   operations. The statement includes empty input or output dimensions, and retains the same scalar list. This is the transposition interface used when preparing stored changes.
--
--   Differences from the source:
--   - encoding: an r×s matrix over R[t]/(t^q) → polynomial matrix representatives with the q-coefficient truncated convolution map; reason: only the first q coefficients are used, so every quotient matrix is represented and changing representatives has no effect
--   - encoding: one can construct a transposed linear program without storing A → the explicit reverse-accumulation compiler and two coefficient-block wire permutations; reason: the implementation exposes the same-scalars and operation-count requirements, and scalar preparation remains separate
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §A.2, Lemma A.2 and following truncated-ring paragraph, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Transposition

namespace AlmostLinearModComp.Composition

/-- Zhou--Wang, Lemma A.2, printed p.11 / PDF p.12.
The compiler has no matrix argument and no access to scalar values. -/
theorem lemma_A_2 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (k r s : ℕ) (p : LinearProgram), p.valid k s r →
        (transposeProgram p s).valid k r s ∧
        ((transposeProgram p s).cost : ℝ) ≤ C * (p.cost + r + s) ∧
        ∀ (R : Type) [CommRing R] (scalars : List R), scalars.length = k →
          ∀ A : Matrix (Fin r) (Fin s) R,
            (∀ x : Fin s → R, p.eval scalars (List.ofFn x) = matrixAction A x) →
            ∀ b : Fin r → R,
              (transposeProgram p s).eval scalars (List.ofFn b) =
                matrixAction A.transpose b) ∧
      (∀ (k r s q : ℕ) (hq : 1 ≤ q) (p : LinearProgram),
        p.valid k (s * q) (r * q) →
        (transposeTruncated p s q).valid k (r * q) (s * q) ∧
        ((transposeTruncated p s q).cost : ℝ) ≤ C * (p.cost + (r + s) * q) ∧
        ∀ (R : Type) [CommRing R] (scalars : List R), scalars.length = k →
          ∀ A : Matrix (Fin r) (Fin s) (Polynomial R),
            (∀ x : Fin s → Fin q → R,
              p.eval scalars ((List.ofFn fun i => List.ofFn (x i)).flatten) =
                coefficientAction q A x) →
            ∀ b : Fin r → Fin q → R,
              (transposeTruncated p s q).eval scalars
                  ((List.ofFn fun i => List.ofFn (b i)).flatten) =
                coefficientAction q A.transpose b) := by sorry

end AlmostLinearModComp.Composition
