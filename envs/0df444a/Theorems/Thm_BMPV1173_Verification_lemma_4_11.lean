-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_4_11
-- name    : BMPV1173.Verification.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:07:34.708494+00:00
-- url     : https://prove2.me/theorems/780ba59f-991b-4972-8369-04e6d63a5ff1
-- title:
--   Lemma 4.11 — general checking correctness and query cost
-- statement:
--   Condition on the simultaneous preprocessing and size-label good events. Given a nonempty $I\subseteq V_a$ and its actual maintained records and left lists, a general checking routine decides whether some $i\in I$ has a distinct orthogonal partner anywhere in the input. Its query cost, with any specified inverse-polynomial error, is
--   $$\widetilde O\!\left(n\sqrt{s+n/t}+\sqrt{nra}\right),\qquad r=|I|.$$
--   One circuit serves every compatible unknown input. Known maintained data are supplied only for indices in $I$, and sampled rows are the fully acquired ones. The result supplies both a correct Boolean decision and a fixed query cap; it does not assume the unknown partner work values or an algorithm that already solves this task.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: query cost for loading, checking or class access with acquired data free → existence of an actual XOR circuit realizing the specified data task uniformly over every input compatible with the acquired data; reason: the source routines leave their quantum search implementations unspecified; the task contract fixes their complete output and resource behavior without postulating correctness or budgets
--   - encoding: arbitrarily high inverse-polynomial subroutine accuracy → error at most (n+1)^(-c) for every requested c>0; reason: this is nontrivial also at n=1 and supplies the source inverse-polynomial accuracy on all larger positive dimensions
--   - generalization: the prescribed independent coordinate sample K → any fixed coordinate list for which the size-label good event holds; reason: these conditional record and checking tasks never query the label sample; the original successful sample is included
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 4.11, printed p.31 = PDF p.31.

import Definitions.Def_BMPV1173_Verification_Access

namespace BMPV1173.Verification

open scoped BigOperators

/-- GeneralCheck's complete decision and resource contract, Lemma 4.11,
pp.31–32. Known maintained data are supplied ONLY on I; good events are
conditional here and are not hypotheses of either main upper bound. -/
theorem lemma_4_11 (c : ℝ) (hc : 0 < c) (cD : ℕ) (hcD : 0 < cD) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (n s t m a : ℕ),
      1 ≤ n → 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n → 2*t ≤ a → a ≤ 4*n →
      (∃ b : ℕ, a = 2^b) →
      ∀ (p : Fin s → Fin n) (g : Fin (sampleCount cD n t) → Fin n)
        (v : SampleValues n s (sampleCount cD n t)) (K : Fin m → Fin n)
        (I : Finset (Fin n)), I.Nonempty →
      ∀ stored : (i : I) → Maintained n s (sampleCount cD n t),
      ∃ T : ℕ,
        HasFunction {x | x ∈ goodInputs p g v s t K ∧
          I ⊆ sizeClass (left x p g t) t K a ∧
          ∀ i : I, stored i = maintainedData x p g t i}
          (hasPartner I) (((n : ℝ)+1)^(-c)) T ∧
        (T : ℝ) ≤ C*((n : ℝ)*Real.sqrt (s+(n : ℝ)/t)+
          Real.sqrt ((n : ℝ)*I.card*a))*(1+Real.log (n : ℝ))^k := by sorry

end BMPV1173.Verification
