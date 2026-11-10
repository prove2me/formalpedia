-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_9
-- name    : ChaChaTree.DynOpt.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:42.122297+00:00
-- url     : https://prove2.me/theorems/4e9af6eb-b70e-4ba3-97bf-5573e88de154
-- title:
--   Lemma 9 — Φ₂ = −(turns + I[switches > 0]) releases DepthAlt_S minus twice the mixed turns of P and P^R
-- statement:
--   Let $\Phi_2(P) := -(\mathrm{turns}(P) + I[\mathrm{switches}(P) > 0])$. For every instance $P$ on $[N]\times[T]$ and every partition $S$ of $[N]$ into contiguous segments,
--   $$\Delta_S \Phi_2(P) \ge \mathrm{DepthAlt}_S(P) - 2\big(\mathrm{mixedturns}_S(P) + \mathrm{mixedturns}_S(P^R)\big),$$
--   where $P^R$ is the time reverse of $P$ (its own $\mathrm{nd}$ and $h$ are computed in $P^R$).
--
--   Differences from the source:
--   - encoding: a partition S = (S_1, …, S_k) of [N] into disjoint contiguous intervals ordered from left to right → a segment map seg : ℕ → ℕ with IsSegmentation N k seg (monotone from [N] onto [k]; S_i = {x ∈ [N] | seg x = i}); reason: monotone and onto [k] is exactly a left-to-right partition into k nonempty contiguous intervals; same instances
--   - encoding: real-valued potentials and differences → integers (ℤ), with the counts cast from ℕ; reason: every quantity involved is an integer; the inequalities are the same
--   - encoding: the indicator I[switches(P) > 0] → if 0 < switches Q then 1 else 0; reason: the same indicator
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 9, p. 13 (PDF 14)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_Split

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 9** (p. 13). For `Φ₂(P) := −(turns(P) + I[switches(P) > 0])` and the split of
an instance `P` on `[N] × [T]` with respect to `S`,
`Δ_S Φ₂(P) ≥ DepthAlt_S(P) − 2(mixedturns_S(P) + mixedturns_S(P^R))`, where `P^R` is the time
reverse of `P`. -/
theorem lemma_9 (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (k : ℕ) (seg : ℕ → ℕ)
    (hS : IsSegmentation N k seg) :
    (depthAltS seg P : ℤ) - 2 * ((mixedturns seg P : ℤ) + mixedturns seg (timeReverse T P)) ≤
      deltaS (fun Q => -((turns Q : ℤ) + if 0 < switches Q then 1 else 0)) k seg P := by sorry

end ChaChaTree.DynOpt
