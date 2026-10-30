-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_virtual_queue_bound
-- name    : CrossLayerControl.ECCA.virtual_queue_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:31.936988+00:00
-- url     : https://prove2.me/theorems/fed1536c-7c87-4441-91c3-0026c1b03663
-- title:
--   Theorem 6.3, clause 2: $D(t)\le\beta V+\beta\hat R+P_{max}$ (corrected: cross-monotone rates; $U(0)\le V+\hat R$)
-- statement:
--   Assume the standing hypotheses of Theorem 6.3 (signs, (3.4), the $\beta$-condition and cross-monotonicity), $V>0$, arrivals $0\le a_i(t)\le\hat R$, initial backlogs $0\le U_i(0)\le V+\hat R$, and let $(r,p)$ be any ECCA run. Then for every slot $t$,
--   $$D(t)\le D_{max}=\beta V+\beta\hat R+P_{max}.$$
--
--   The virtual power queue of ECCA is bounded deterministically, for any state and arrival sequences. This is the second clause of Theorem 6.3, and the energy bound follows from it.
--
--   Differences from the source:
--   - correction: β-condition only → β-condition plus cross-monotonicity C_j(P,s) ≤ C_j(P[i],s) for j ≠ i (DownlinkHyp); reason: the printed claim is false: L = 2, Pmax = 1, Pav = 0.5, β = 0.01, V = 10, R̂ = 1, µmax = 1, C_1 ≡ 0, C_2(P) = 1[P_1 ≥ 1], A ≡ (0,1) satisfies every printed assumption, ECCA allocates P = (1,0) with D(t) > βU_1(t), and D(t) reaches 10 > βV + βR̂ + Pmax = 1.11
--   - correction: U(0) unstated → 0 ≤ U_i(0) ≤ V + R̂; reason: with U_i(0) = V + R̂ + 1 the bound U_i(t) ≤ V + R̂ fails at t = 0
--   - reading: signs of Pav, Pmax, R̂ unstated → 0 ≤ Pav, 0 ≤ Pmax, 0 ≤ R̂ (RateHyp); reason: a negative average power budget is unsatisfiable; R̂ ≥ 0 is forced by 0 ≤ A_i ≤ R̂ when L ≥ 1 and keeps L = 0 nondegenerate; Pmax ≥ 0 follows from 0 ≤ Pav < Pmax
--   - generalization: ECCA with the rule admit everything iff U_i(t) ≤ V and a maximizer of (6.14) → any minimizer of the flow-control objective and any maximizer of (6.14) (IsECCARun); reason: ties broken arbitrarily; the paper's run is one of these
--   - generalization: Pav < Pmax; topology state set finite (p. 27) → Pav < Pmax not assumed; state space an arbitrary type; reason: no step uses them; the source's setting is a special case
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - encoding: A_i(t) ≤ R̂ → 0 ≤ A_i(t) ≤ R̂; reason: arrivals are amounts of data, hence nonnegative; with A_i(t) < 0 the flow-control constraint 0 ≤ R_i(t) ≤ A_i(t) is infeasible and no ECCA run (or admissible decision) exists, so no instance is excluded
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115, second display

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun

namespace CrossLayerControl.ECCA

/-- **ECCA keeps the virtual power queue below Dmax = βV + βR̂ + Pmax (Theorem 6.3, clause 2).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115, second display: "D(t) ≤ Dmax ≜ βV + βR̂ + Pmax
for all t."

Under the standing assumptions `DownlinkHyp M`, with `V > 0`, arrivals `0 ≤ aᵢ(t) ≤ R̂`, initial
backlogs `0 ≤ Uᵢ(0) ≤ V + R̂`, and an ECCA run, for every slot `t`,
`D(t) ≤ βV + βR̂ + Pmax`.

**Formalization Note.** This is the second clause of Theorem 6.3; the goal theorem restates it. It
rests on corrections C1 (cross-monotonicity, in `DownlinkHyp`) and C2 (`Uᵢ(0) ≤ V + R̂`). -/
theorem virtual_queue_bound {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : DownlinkHyp M)
    (V : ℝ) (hV : 0 < V) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (ha : ∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) (hrun : IsECCARun M V u₀ a s r p) :
    ∀ t, virtD M p t ≤ M.β * V + M.β * M.Rhat + M.Pmax := by sorry

end CrossLayerControl.ECCA
