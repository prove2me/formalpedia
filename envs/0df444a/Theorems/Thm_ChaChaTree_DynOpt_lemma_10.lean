-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_10
-- name    : ChaChaTree.DynOpt.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:42.066922+00:00
-- url     : https://prove2.me/theorems/ac3cac56-1382-467b-98e7-2480858df046
-- title:
--   Lemma 10 — Φ₃ = 5·SIR releases at least 2(mixedturns(P) + mixedturns(P^R)) − 4·doubleswitches
-- statement:
--   Let $\Phi_3(P) := 5\,\mathrm{SIR}(P)$. For every instance $P$ on $[N]\times[T]$ and every partition $S$ of $[N]$ into contiguous segments,
--   $$\Delta_S \Phi_3(P) \ge 2\big(\mathrm{mixedturns}_S(P) + \mathrm{mixedturns}_S(P^R)\big) - 4\,\mathrm{doubleswitches}_S(P).$$
--
--   Differences from the source:
--   - encoding: a partition S = (S_1, …, S_k) of [N] into disjoint contiguous intervals ordered from left to right → a segment map seg : ℕ → ℕ with IsSegmentation N k seg (monotone from [N] onto [k]; S_i = {x ∈ [N] | seg x = i}); reason: monotone and onto [k] is exactly a left-to-right partition into k nonempty contiguous intervals; same instances
--   - encoding: real-valued potentials and differences → integers (ℤ), with the counts cast from ℕ; reason: every quantity involved is an integer; the inequalities are the same
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 10, p. 14 (PDF 15); proof p. 19 (PDF 20)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_Split

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 10** (p. 14). For `Φ₃(P) := 5 SIR(P)` and the split of an instance `P` on
`[N] × [T]` with respect to `S`,
`Δ_S Φ₃(P) ≥ 2(mixedturns_S(P) + mixedturns_S(P^R)) − 4 doubleswitches_S(P)`. -/
theorem lemma_10 (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (k : ℕ) (seg : ℕ → ℕ)
    (hS : IsSegmentation N k seg) :
    2 * ((mixedturns seg P : ℤ) + mixedturns seg (timeReverse T P)) -
        4 * (doubleswitches seg P : ℤ) ≤
      deltaS (fun Q => 5 * (SIR Q : ℤ)) k seg P := by sorry

end ChaChaTree.DynOpt
