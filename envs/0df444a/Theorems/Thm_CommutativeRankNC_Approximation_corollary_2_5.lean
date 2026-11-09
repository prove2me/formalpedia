-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_corollary_2_5
-- name    : CommutativeRankNC.Approximation.corollary_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:56.620888+00:00
-- url     : https://prove2.me/theorems/27ae9f60-8a96-4a24-88f3-82782afbe275
-- title:
--   Corollary 2.5 — Uniform parallel sign family
-- statement:
--   For each fixed positive integer $t$, the canonical seed image $H_{m,t}$, in the section's regime $m\ge2$, is $t$-wise unbiased and has
--
--   $$|H_{m,t}|\le q^t<(2m)^t.$$
--
--   There is one logspace-uniform Boolean NC² family that outputs the entire seed-indexed sign table for every $m$. The constants can depend on fixed $t$, but not on $m$. The finite law is the uniform seed pushforward, with support equal to the image. The separate $m=1$ convention remains in the definitions and does not assert the strict $q<2m$ inequality there.
--
--   Differences from the source:
--   - encoding: elements of the quotient field F₂[z]/(f) → binary coefficient representatives, finite trial division, and reduction modulo the first irreducible polynomial; reason: these are the explicit field representation and deterministic search in the proof of Lemma 2.1; no arithmetic oracle is used
--   - encoding: probabilities and expectations for a finite sign distribution → finite real weighted sums, with seed multiplicities retained in the pushforward law; reason: a finite law needs no analytic integrability assumption and does not replace the seed law by a uniform distinct-image law
--   - encoding: a uniformly constructible sample space → its explicit seed-indexed table, including repeated rows; reason: the induced distribution retains precisely the source seed probabilities; producing the table also enumerates its support
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Corollary 2.5, PDF/printed p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_ConstructionCodes

namespace CommutativeRankNC.Approximation

/-- Corollary 2.5, PDF/printed p.11, under the section's m≥2 setup.
The m=1 footnote is used by the totalized definitions elsewhere. -/
theorem corollary_2_5 (t : ℕ) (ht : 0 < t) :
    ∃ F : (N : ℕ) → BooleanCircuit N, BooleanNC 2 F ∧
      ∀ m : ℕ, 2 ≤ m →
        (signSupport m t).card ≤ fieldCard m ^ t ∧
        fieldCard m ^ t < (2*m) ^ t ∧
        TWiseUnbiased t (signWeight m t) ∧
        booleanEval (F m) (List.replicate m true) = signTableCode m t := by sorry

end CommutativeRankNC.Approximation
