-- Prove2me | Theorems.Thm_AlmostLinearModComp_Composition_lemma_3_1
-- name    : AlmostLinearModComp.Composition.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:20.371816+00:00
-- url     : https://prove2.me/theorems/b6edaa23-8bbd-484b-84e8-3a4974aa5d8c
-- title:
--   Lemma 3.1 — Coordinate change
-- statement:
--   There are absolute $C>0$, $k\in\mathbb N$ and one size-indexed family of integer-scalar bilinear programs with the following property over every commutative ring $R$. At any admissible step $2v\to v$, for every $1\le q\le L$, supply the modulus $F$ and exactly the array entries $M(\gamma)\bmod t^q$ of equation (6), with side $3s_j$ at digit $j$ and $2s_i$ elsewhere, including the last coordinate. The specified convolution and precision-only Hensel circuit returns every coefficient of
--   $$T_{2v}p\pmod {t^q}.$$
--
--   Its fixed-data preparation produces a valid linear program for that map and a valid transposed program. Both use at most
--   $$C\,2^mNq\,(1+\log_2(Nq+2))^k$$
--   operations in $R$. Both programs use precisely the scalar list computed from $F$ and this array. The transpose includes coefficient-block reversal; no matrix is supplied. Targets may be any canonical quotient representatives congruent to $X^{w_i}$ modulo $t$, as needed for Proposition 4.1. The recursive routine keeps the stored data fixed and decreases only precision. All constants and the raw implementation family precede the varying parameters and rings.
--
--   Differences from the source:
--   - generalization: Section 3 uses the targets constructed in equation (1) → arbitrary targets congruent to X^w_i modulo t; reason: Proposition 4.1 explicitly requires the same coordinate and preparation routines for this domain; taking the constructed targets recovers every Section 3 instance
--   - encoding: elements of R[t]/(t^L)[X]/(F) and vectors in its monomial basis → polynomial representatives with degree-below-N X coefficients, read in coordinate-major t blocks; reason: each quotient element has a unique such finite coefficient array; only its first L coefficients in t are read
--   - encoding: standard arithmetic routines expanded into ring operations → raw size-indexed bilinear programs spliced into actual circuits, with existence of a suitable family in the conclusion; reason: no arithmetic correctness or complexity is assumed; all gates and fixed-data preparation are exposed and counted
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), Lemma 3.1 and preceding routine, printed pp.5–7 / PDF pp.6–8; Proposition 4.1, printed p.8 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_CoordinateAlgorithm

namespace AlmostLinearModComp.Composition

/-- Zhou--Wang, Lemma 3.1, printed p.7 / PDF p.8. The preceding equations
(5)--(9) and the precision-only Hensel recursion are implemented in coordinateW.
The compatible-target generality is also required by Proposition 4.1. -/
theorem lemma_3_1 :
    ∃ (C : ℝ) (k : ℕ) (B : Multipliers), 0 < C ∧
      ∀ (d : Radices) (s : Stage d) (L q : ℕ), 1 ≤ q → q ≤ L →
        let plan := changePlan B s q q
        let p := plan.2
        plan.1.valid (d.size + s.arraySize * q) plan.1.outputs.length ∧
        (coordinateCircuit B s q q).valid
          (d.size + s.arraySize * q + d.size * q) (d.size * q) ∧
        p.valid plan.1.outputs.length (d.size * q) (d.size * q) ∧
        (transposeTruncated p d.size q).valid
          plan.1.outputs.length (d.size * q) (d.size * q) ∧
        (p.cost : ℝ) ≤ evaluationBound C k d.size q (2 ^ d.m) ∧
        ((transposeTruncated p d.size q).cost : ℝ) ≤
          evaluationBound C k d.size q (2 ^ d.m) ∧
        ∀ (R : Type) [CommRing R] (F : Polynomial R)
          (a : Fin d.m → Polynomial (Polynomial R)),
          F.Monic → F.degree = (d.size : WithBot ℕ) →
          CompatibleTargets d a → CanonicalTargets d L a →
          ∀ x : Fin d.size → Fin q → R,
            let data := (List.ofFn fun i : Fin d.size => F.coeff i) ++ canonicalArray s F q a
            let input := (List.ofFn fun i => List.ofFn (x i)).flatten
            let T := coordinateMatrix s F L a
            (coordinateCircuit B s q q).eval (data ++ input) = coefficientAction q T x ∧
            p.eval (plan.1.eval data) input = coefficientAction q T x ∧
            (transposeTruncated p d.size q).eval (plan.1.eval data) input =
              coefficientAction q T.transpose x := by sorry

end AlmostLinearModComp.Composition
