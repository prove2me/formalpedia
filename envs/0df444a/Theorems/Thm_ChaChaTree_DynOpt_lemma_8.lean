-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_8
-- name    : ChaChaTree.DynOpt.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:35.981235+00:00
-- url     : https://prove2.me/theorems/b7bc7b5f-b0bb-4557-921b-b68c974cde7e
-- title:
--   Lemma 8 — Φ₁ = −4·switches releases exactly 4·doubleswitches_S under a split
-- statement:
--   Let $\Phi_1(P) := -4\,\mathrm{switches}(P)$. For every instance $P$ on $[N] \times [T]$ and every partition $S$ of $[N]$ into $k$ contiguous segments,
--   $$\Delta_S \Phi_1(P) = 4\,\mathrm{doubleswitches}_S(P).$$
--
--   Differences from the source:
--   - encoding: a partition S = (S_1, …, S_k) of [N] into disjoint contiguous intervals ordered from left to right → a segment map seg : ℕ → ℕ with IsSegmentation N k seg (monotone from [N] onto [k]; S_i = {x ∈ [N] | seg x = i}); reason: monotone and onto [k] is exactly a left-to-right partition into k nonempty contiguous intervals; same instances
--   - encoding: real-valued potentials and differences → integers (ℤ), with the counts cast from ℕ; reason: every quantity involved is an integer; the inequalities are the same
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 8, pp. 12–13 (PDF 13–14)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_Split

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 8** (pp. 12–13). For `Φ₁(P) := −4 switches(P)` and the split of an instance `P` with
respect to a partition `S` of `[N]` into `k` contiguous segments,
`Δ_S Φ₁(P) = 4 doubleswitches_S(P)`. -/
theorem lemma_8 (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (k : ℕ) (seg : ℕ → ℕ)
    (hS : IsSegmentation N k seg) :
    deltaS (fun Q => -4 * (switches Q : ℤ)) k seg P = 4 * (doubleswitches seg P : ℤ) := by sorry

end ChaChaTree.DynOpt
