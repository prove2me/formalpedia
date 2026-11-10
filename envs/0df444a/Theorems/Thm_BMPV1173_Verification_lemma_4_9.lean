-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_4_9
-- name    : BMPV1173.Verification.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:07:54.996475+00:00
-- url     : https://prove2.me/theorems/169d8cfd-54c5-4d64-9600-af30a8baa662
-- title:
--   Lemma 4.9 — record loading and maintained data
-- statement:
--   Given only the fully read pivot and degree-sample rows, a record-loading query routine produces $\mathrm{record}(i)=(\mathrm{first}(i,p))_{p\in\mathrm{Pivots}\sqcup\mathrm{DegSamp}}$ in
--   $$\widetilde O\!\left(\sqrt{n(s+n/t)}\right)$$
--   queries. Every sampled occurrence is retained, including repeats and self occurrences. The record, together with known sampled rows, determines covered and heavy membership at every coordinate and determines $\mathrm{Right}_i$. Conditioned on the source good events, for $i\in V_a$, loading the complete maintained pair $(\mathrm{record}(i),\mathrm{Left}_i)$ costs
--   $$\widetilde O\!\left(\sqrt{na}+\sqrt{n(s+n/t)}\right).$$
--   The circuits succeed with any specified inverse-polynomial error uniformly over all unknown inputs compatible with the acquired sample rows. Record loading itself does not assume the good events; only the maintained-data bound uses them.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: query cost for loading, checking or class access with acquired data free → existence of an actual XOR circuit realizing the specified data task uniformly over every input compatible with the acquired data; reason: the source routines leave their quantum search implementations unspecified; the task contract fixes their complete output and resource behavior without postulating correctness or budgets
--   - encoding: record determines membership and the right list → explicit decoders from sampled rows and record comparisons, with exact identities; reason: the only completion used for decoding is formed from the known sampled rows, so no unknown row is supplied for free
--   - encoding: arbitrarily high inverse-polynomial subroutine accuracy → error at most (n+1)^(-c) for every requested c>0; reason: this is nontrivial also at n=1 and supplies the source inverse-polynomial accuracy on all larger positive dimensions
--   - generalization: the prescribed independent coordinate sample K → any fixed coordinate list for which the size-label good event holds; reason: these conditional record and checking tasks never query the label sample; the original successful sample is included
--   - generalization: the sampled-row record decoding identities → decoding identities for every finite sample length, including zero; reason: the identities require only actual record entries and consistent sampled rows; the query-cost clauses still use the source sampling scale
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 4.9, printed p.29 = PDF p.29.

import Definitions.Def_BMPV1173_Verification_Access

namespace BMPV1173.Verification

open scoped BigOperators

/-- Record loading and all information determined by a record, Lemma 4.9,
pp.29–30. The sample rows alone are free side information. -/
theorem lemma_4_9 (c : ℝ) (hc : 0 < c) (cD : ℕ) (hcD : 0 < cD) :
    (∀ (n s d t : ℕ) (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
      (i k : Fin n),
      (coveredFromRecord (sampleValues x p g) (record x p g i) k ↔ i ∈ covered x p k) ∧
      (heavyFromRecord p g (sampleValues x p g) (record x p g i) t k ↔ i ∈ heavy x p g t k) ∧
      rightFromRecord (record x p g i) = right x p i) ∧
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (n s t : ℕ),
      1 ≤ n → 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n →
      ∀ (p : Fin s → Fin n) (g : Fin (sampleCount cD n t) → Fin n)
        (v : SampleValues n s (sampleCount cD n t)) (i : Fin n),
      (∃ T : ℕ, HasFunction (compatibleSamples p g v) (fun x => record x p g i)
          (((n : ℝ)+1)^(-c)) T ∧
        (T : ℝ) ≤ C*Real.sqrt ((n : ℝ)*(s+(n : ℝ)/t))*(1+Real.log (n : ℝ))^k) ∧
      ∀ (m a : ℕ) (K : Fin m → Fin n),
        ∃ T : ℕ,
          HasFunction {x | x ∈ goodInputs p g v s t K ∧
            i ∈ sizeClass (left x p g t) t K a}
            (fun x => maintainedData x p g t i) (((n : ℝ)+1)^(-c)) T ∧
          (T : ℝ) ≤ C*(Real.sqrt ((n : ℝ)*a)+
            Real.sqrt ((n : ℝ)*(s+(n : ℝ)/t)))*(1+Real.log (n : ℝ))^k := by sorry

end BMPV1173.Verification
