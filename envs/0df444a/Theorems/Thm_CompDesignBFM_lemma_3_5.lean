-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_3_5
-- name    : CompDesignBFM.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:33:12.927437+00:00
-- url     : https://prove2.me/theorems/40e734f8-30d2-47c9-b2b6-447788eb771d
-- title:
--   Lemma 3.5 — the sum of marginals of the smoothed value
-- statement:
--   For every normalized set function $v$ and its smoothed value $\tilde v$, for every $S\subseteq N$,
--
--   $$\sum_{i\in S}\bigl(\tilde v(S)-\tilde v(S\setminus\{i\})\bigr)=v(S)-\tilde v(S).$$
--
--   Together with $v\le2\tilde v$ this gives the self-bounding property of $\tilde v$.
--
--   Differences from the source:
--   - generalization: v : 2^N → ℝ≥0 (Definition 3.1) → v real-valued with v ∅ = 0; reason: the identity is linear in the values of v, so no sign is needed; nonnegative v are instances
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 3.5, p.19 (PDF 21)

import Mathlib
import Definitions.Def_CompDesignBFM_smoothed

namespace CompDesignBFM

/-- Lemma 3.5, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.19, PDF 21 (proof p.51, PDF 53). For every normalized set function `v` and its smoothed
value `ṽ`, for every `S ⊆ N`, `∑ i ∈ S, (ṽ S - ṽ (S ∖ {i})) = v S - ṽ S`.
**Formalization Note.** `v` is real-valued, with no sign or monotonicity assumption. -/
theorem lemma_3_5 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (S : Finset (Fin n)) :
    ∑ i ∈ S, (smoothed v S - smoothed v (S.erase i)) = v S - smoothed v S := by sorry

end CompDesignBFM
