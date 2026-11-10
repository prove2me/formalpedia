-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_15
-- name    : ChaChaTree.DynOpt.lemma_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:35.107488+00:00
-- url     : https://prove2.me/theorems/46e1c148-e253-4a0f-a956-ee69d9fc3517
-- title:
--   Lemma 15 — SIR is superadditive under a split, with bonus max{0, mixedturns − doubleswitches}
-- statement:
--   For a split of an instance $P$ with respect to $S$,
--   $$\mathrm{SIR}(P) \ge \mathrm{SIR}(\hat P) + \sum_{i\in[k]} \mathrm{SIR}(\check P_i) + \max\{0,\ \mathrm{mixedturns}_S(P) - \mathrm{doubleswitches}_S(P)\}.$$
--
--   Differences from the source:
--   - encoding: a partition S = (S_1, …, S_k) of [N] into disjoint contiguous intervals ordered from left to right → a segment map seg : ℕ → ℕ with IsSegmentation N k seg (monotone from [N] onto [k]; S_i = {x ∈ [N] | seg x = i}); reason: monotone and onto [k] is exactly a left-to-right partition into k nonempty contiguous intervals; same instances
--   - encoding: real-valued potentials and differences → integers (ℤ), with the counts cast from ℕ; reason: every quantity involved is an integer; the inequalities are the same
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 15, p. 18 (PDF 19)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_Split

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 15** (p. 18). For a split of an instance `P` with respect to `S`,
`SIR(P) ≥ SIR(P̂) + Σ_{i∈[k]} SIR(P̌_i) + max{0, mixedturns_S(P) − doubleswitches_S(P)}`. -/
theorem lemma_15 (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (k : ℕ) (seg : ℕ → ℕ)
    (hS : IsSegmentation N k seg) :
    (SIR (contracted seg P) : ℤ) + (∑ i ∈ Finset.Icc 1 k, (SIR (filtered seg P i) : ℤ)) +
        max 0 ((mixedturns seg P : ℤ) - doubleswitches seg P) ≤ SIR P := by sorry

end ChaChaTree.DynOpt
