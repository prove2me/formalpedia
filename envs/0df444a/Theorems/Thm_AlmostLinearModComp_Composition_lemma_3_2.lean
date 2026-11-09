-- Prove2me | Theorems.Thm_AlmostLinearModComp_Composition_lemma_3_2
-- name    : AlmostLinearModComp.Composition.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:37.395492+00:00
-- url     : https://prove2.me/theorems/9c1b2745-85dc-43a5-b8c1-0f10b493c47b
-- title:
--   Lemma 3.2 — Array construction
-- statement:
--   There are absolute $C>0$, $k\in\mathbb N$ and one size-indexed family of integer-scalar bilinear programs such that, for every radix list, admissible step $2v\to v$, positive precision $L$, and commutative ring $R$, the specified block circuit constructs the entire next array $M$ from $F$, compatible targets, and the arrays belonging to earlier changes. Its operation count, including the reconstruction of the earlier fixed-scalar programs, satisfies
--   $$\operatorname{cost}\le CNL4^m(1+\log_2(NL+2))^k.$$
--
--   The returned list contains every displayed array entry and every one of its $L$ coefficients. Common factors are computed, and each block applies $H$ followed by the previously stored transposes in source order. The next array is never an input. When $v=1$, the earlier-stage list is empty. This prepares the fixed data for the next coordinate change without forming a dense matrix.
--
--   Differences from the source:
--   - generalization: Section 3 uses the targets constructed in equation (1) → arbitrary targets congruent to X^w_i modulo t; reason: Proposition 4.1 explicitly requires the same coordinate and preparation routines for this domain; taking the constructed targets recovers every Section 3 instance
--   - encoding: elements of R[t]/(t^L)[X]/(F) and vectors in its monomial basis → polynomial representatives with degree-below-N X coefficients, read in coordinate-major t blocks; reason: each quotient element has a unique such finite coefficient array; only its first L coefficients in t are read
--   - encoding: standard arithmetic routines expanded into ring operations → raw size-indexed bilinear programs spliced into actual circuits, with existence of a suitable family in the conclusion; reason: no arithmetic correctness or complexity is assumed; all gates and fixed-data preparation are exposed and counted
--   - generalization: earlier changes supplied with their arrays and the Lemma 3.1 cost bound → earlier arrays are inputs and their concrete programs are reconstructed by the same coordinate compiler; reason: the reconstruction is charged within the displayed bound; no arbitrary procedure or correctness certificate is accepted
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), Lemma 3.2 and equation (10), printed p.7 / PDF p.8; Proposition 4.1, printed p.8 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_EvaluationAlgorithm

namespace AlmostLinearModComp.Composition

/-- Zhou--Wang, Lemma 3.2, printed p.7 / PDF p.8. The only supplied arrays
belong to earlier stages. At v=1 their list is empty. The entire next array,
including all t-coefficients, is computed by the actual block routine. -/
theorem lemma_3_2 :
    ∃ (C : ℝ) (k : ℕ) (B : Multipliers), 0 < C ∧
      ∀ (d : Radices) (s : Stage d) (L : ℕ), 1 ≤ L →
        let c := arrayCircuit B s L
        c.valid (d.size + d.m * d.size * L +
          ((earlierStages s).map fun u => u.arraySize * L).sum) (s.arraySize * L) ∧
        (c.cost : ℝ) ≤ evaluationBound C k d.size L (4 ^ d.m) ∧
        ∀ (R : Type) [CommRing R] (F : Polynomial R)
          (a : Fin d.m → Polynomial (Polynomial R)),
          F.Monic → F.degree = (d.size : WithBot ℕ) →
          CompatibleTargets d a → CanonicalTargets d L a →
          c.eval ((List.ofFn fun i : Fin d.size => F.coeff i) ++ targetVector d L a ++
            ((earlierStages s).map fun u => canonicalArray u F L a).flatten) =
            canonicalArray s F L a := by sorry

end AlmostLinearModComp.Composition
