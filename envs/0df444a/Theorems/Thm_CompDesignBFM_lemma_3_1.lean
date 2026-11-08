-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_3_1
-- name    : CompDesignBFM.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:33:10.868871+00:00
-- url     : https://prove2.me/theorems/84fc08da-8ae3-4ed4-ada0-4bbb96113f94
-- title:
--   Lemma 3.1 — marginals of submodular functions
-- statement:
--   For every normalized monotone submodular valuation $v$ and every $S\subseteq N$,
--
--   $$\sum_{i\in S}\bigl(v(S)-v(S\setminus\{i\})\bigr)\le v(S).$$
--
--   So monotone submodular functions are self-bounding, and the marginal-contribution rule on $v$ is budget feasible.
--
--   Differences from the source: none.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 3.1, p.13 (PDF 15)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF

namespace CompDesignBFM

/-- Lemma 3.1, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.13, PDF 15. For every normalized monotone submodular valuation and every `S ⊆ N`,
`∑ i ∈ S, (v S - v (S ∖ {i})) ≤ v S`. -/
theorem lemma_3_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (hm : IsMonotoneSF v)
    (hs : IsSubmodularSF v) (S : Finset (Fin n)) :
    ∑ i ∈ S, (v S - v (S.erase i)) ≤ v S := by sorry

end CompDesignBFM
