-- Prove2me | Theorems.Thm_AlmostLinearModComp_Composition_proposition_4_1
-- name    : AlmostLinearModComp.Composition.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:39.85962+00:00
-- url     : https://prove2.me/theorems/0ea563ce-8647-415e-aa80-c67f5e995e13
-- title:
--   Proposition 4.1 — Evaluation algorithm
-- statement:
--   There are absolute $C>0$, $k\in\mathbb N$ and one size-indexed family of integer-scalar bilinear programs with the following property. Let $R$ be any commutative ring, $N$ the product of positive power-of-two radices $d_i\ge2$, $F$ any monic degree-$N$ polynomial, $L\ge1$, and $S=R[t]/(t^L)$. For every target $a_i\in S[X]/(F)$ congruent to $X^{w_i}$ modulo $t$, and every $P\in S[z_0,\ldots,z_{m-1}]$ of degree below $d_i$ in each variable, the actual two-pass circuit returns all $N$ monomial coefficients of
--   $$P(a_0,\ldots,a_{m-1})\in S[X]/(F).$$
--
--   Each output coefficient is returned with all its $L$ coefficients in $R$. The single circuit has cost at most
--   $$CNL4^m(1+\log_2(NL+2))^k,$$
--   including every stored-array construction, fixed-scalar preparation and both passes. There is no hypothesis asserting fast multiplication, ready-made arrays or a correct low-cost evaluator. Radices need not be balanced, and the targets and precision are not restricted to the headline theorem's particular deformation. Any degree-$N$ monic $F$ occurs in Section 2 by taking its original degree $n=N$, so this modulus presentation loses no source assumption.
--
--   Differences from the source:
--   - encoding: elements of R[t]/(t^L)[X]/(F) and vectors in its monomial basis → polynomial representatives with degree-below-N X coefficients, read in coordinate-major t blocks; reason: each quotient element has a unique such finite coefficient array; only its first L coefficients in t are read
--   - encoding: standard arithmetic routines expanded into ring operations → raw size-indexed bilinear programs spliced into actual circuits, with existence of a suitable family in the conclusion; reason: no arithmetic correctness or complexity is assumed; all gates and fixed-data preparation are exposed and counted
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), Proposition 4.1 and Algorithm 1, printed p.8 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_EvaluationAlgorithm

namespace AlmostLinearModComp.Composition

/-- Zhou--Wang, Proposition 4.1, printed p.8 / PDF p.9. The actual two-pass
circuit computes and pays for every array and every scalar preparation. -/
theorem proposition_4_1 :
    ∃ (C : ℝ) (k : ℕ) (B : Multipliers), 0 < C ∧
      ∀ (d : Radices) (L : ℕ), 1 ≤ L →
        let c := algorithmOneCircuit B d L
        c.valid (d.size + d.m * d.size * L + d.size * L) (d.size * L) ∧
        (c.cost : ℝ) ≤ evaluationBound C k d.size L (4 ^ d.m) ∧
        ∀ (R : Type) [CommRing R] (F : Polynomial R)
          (a : Fin d.m → Polynomial (Polynomial R))
          (P : MvPolynomial (Fin d.m) (Polynomial R)),
          F.Monic → F.degree = (d.size : WithBot ℕ) →
          CompatibleTargets d a → CanonicalTargets d L a →
          (∀ alpha ∈ P.support, ∀ i, alpha i < d.digitBound i) →
          c.eval ((List.ofFn fun i : Fin d.size => F.coeff i) ++
            targetVector d L a ++ outerVector d L P) = evaluationVector d L F a P := by sorry

end AlmostLinearModComp.Composition
