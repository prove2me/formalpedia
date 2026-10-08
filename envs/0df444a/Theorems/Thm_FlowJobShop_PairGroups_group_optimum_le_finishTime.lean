-- Prove2me | Theorems.Thm_FlowJobShop_PairGroups_group_optimum_le_finishTime
-- name    : FlowJobShop.PairGroups.group_optimum_le_finishTime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:54:56.957004+00:00
-- url     : https://prove2.me/theorems/060a3e3b-a4cb-45ed-8bc2-f247ded5807f
-- title:
--   Proof of Lemma 11 — $\mathrm{FT}(S^*)\ge\max_g f(R(g))$
-- statement:
--   Let $F$ be a flow shop with $m$ processors and $n$ jobs, and for every group $g=1,\dots,\lceil m/2\rceil$ let $R(g)$ be an optimal finish time schedule of the flow shop $F_g$ on the processor pair $P_{2g-1},P_{2g}$, with finish time $f(R(g))$. Then for every feasible non-preemptive schedule $\tau$ of $F$ (in particular for an OFT schedule $S^*$),
--   $$\max\Big(0,\ \max_{g} f(R(g))\Big)\le \mathrm{FT}(\tau).$$
--
--   This is the lower bound on the optimum used in the proof of Lemma 11.
--
--   **Formalization Note** The maximum is a fold of `max` with baseline $0$ over the $\lceil m/2\rceil$ groups, so it is $0$ when $m=0$; all finish times are nonnegative, so the baseline changes nothing otherwise.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 49, §2, proof of Lemma 11

import Mathlib
import Definitions.Def_FlowJobShop_PairGroups_FlowShop
import Definitions.Def_FlowJobShop_PairGroups_AlgorithmH

namespace FlowJobShop.PairGroups

open FlowShop

/-- Proof of Lemma 11 (p. 49): the finish time of an optimal schedule of the flow shop on any
processor group is at most the finish time of any feasible schedule of the whole flow shop;
hence `FT(S*) ≥ max_g f(R(g))`. -/
theorem group_optimum_le_finishTime {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsOptimal (R g))
    (τ : Fin m → Fin n → ℝ) (hτ : F.IsFeasible τ) :
    (Finset.univ : Finset (Fin ((m + 1) / 2))).fold max 0
        (fun g => (F.group g).finishTime (R g)) ≤ F.finishTime τ := by sorry

end FlowJobShop.PairGroups
