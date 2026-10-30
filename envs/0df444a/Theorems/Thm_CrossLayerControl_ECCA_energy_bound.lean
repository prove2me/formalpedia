-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_energy_bound
-- name    : CrossLayerControl.ECCA.energy_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:22.936512+00:00
-- url     : https://prove2.me/theorems/2f7b7682-52f8-4e09-9d79-132f77391232
-- title:
--   Theorem 6.3, clause 3: energy over any $T$ slots is at most $P_{av}T+D_{max}$ (corrected: cross-monotone rates; $U(0)\le V+\hat R$)
-- statement:
--   Under the hypotheses of the virtual-queue bound (standing hypotheses of Theorem 6.3, $V>0$, $0\le a_i(t)\le\hat R$, $0\le U_i(0)\le V+\hat R$, an ECCA run $(r,p)$), with $D_{max}=\beta V+\beta\hat R+P_{max}$:
--
--   1. for every starting slot $t_0$ and every length $T$,
--   $$\sum_{\tau=t_0}^{t_0+T-1}\sum_{i=1}^L P_i(\tau)\le P_{av}T+D_{max};$$
--   2. the average power constraint holds:
--   $$\limsup_{T\to\infty}\frac1T\sum_{\tau=0}^{T-1}\sum_{i=1}^L P_i(\tau)\le P_{av}.$$
--
--   ECCA meets the average power constraint on every sample path, with a worst-case excess of $D_{max}$ over any window.
--
--   Differences from the source:
--   - correction: β-condition only → β-condition plus cross-monotonicity C_j(P,s) ≤ C_j(P[i],s) for j ≠ i (DownlinkHyp); reason: the printed claim is false: L = 2, Pmax = 1, Pav = 0.5, β = 0.01, V = 10, R̂ = 1, µmax = 1, C_1 ≡ 0, C_2(P) = 1[P_1 ≥ 1], A ≡ (0,1) satisfies every printed assumption, ECCA allocates P = (1,0) with D(t) > βU_1(t), and D(t) reaches 10 > βV + βR̂ + Pmax = 1.11
--   - correction: U(0) unstated → 0 ≤ U_i(0) ≤ V + R̂; reason: with U_i(0) = V + R̂ + 1 the bound U_i(t) ≤ V + R̂ fails at t = 0
--   - reading: signs of Pav, Pmax, R̂ unstated → 0 ≤ Pav, 0 ≤ Pmax, 0 ≤ R̂ (RateHyp); reason: a negative average power budget is unsatisfiable; R̂ ≥ 0 is forced by 0 ≤ A_i ≤ R̂ when L ≥ 1 and keeps L = 0 nondegenerate; Pmax ≥ 0 follows from 0 ≤ Pav < Pmax
--   - reading: the average power constraint clearly holds → limsup_{T→∞} (1/T) Σ_{τ<T} Σ_i P_i(τ) ≤ Pav, in EReal; reason: the paper's average power constraint is a time average of the power; EReal makes the limsup honest
--   - generalization: ECCA with the rule admit everything iff U_i(t) ≤ V and a maximizer of (6.14) → any minimizer of the flow-control objective and any maximizer of (6.14) (IsECCARun); reason: ties broken arbitrarily; the paper's run is one of these
--   - generalization: Pav < Pmax; topology state set finite (p. 27) → Pav < Pmax not assumed; state space an arbitrary type; reason: no step uses them; the source's setting is a special case
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - encoding: A_i(t) ≤ R̂ → 0 ≤ A_i(t) ≤ R̂; reason: arrivals are amounts of data, hence nonnegative; with A_i(t) < 0 the flow-control constraint 0 ≤ R_i(t) ≤ A_i(t) is infeasible and no ECCA run (or admissible decision) exists, so no instance is excluded
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115 (sentence after the displays)

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun

open Filter

namespace CrossLayerControl.ECCA

/-- **The energy spent by ECCA over any T slots is at most Pav·T + Dmax (Theorem 6.3, clause 3).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115 (unnumbered sentence): "Consequently, the
energy expended over any interval of T slots is never more than PavT + Dmax (and so the average
power constraint clearly holds)."

Under the standing assumptions `DownlinkHyp M`, with `V > 0`, arrivals `0 ≤ aᵢ(t) ≤ R̂`, initial
backlogs `0 ≤ Uᵢ(0) ≤ V + R̂`, and an ECCA run:
1. for every start slot `t₀` and length `T`,
   `Σ_{τ = t₀}^{t₀+T−1} Σᵢ Pᵢ(τ) ≤ Pav·T + (βV + βR̂ + Pmax)`;
2. `limsup_{T→∞} (1/T) Σ_{τ<T} Σᵢ Pᵢ(τ) ≤ Pav`.

**Formalization Note.** The `limsup` is taken in `EReal`, so it is never a junk value. The bound
rests on corrections C1 and C2 through `D(t) ≤ Dmax`. -/
theorem energy_bound {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : DownlinkHyp M)
    (V : ℝ) (hV : 0 < V) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (ha : ∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) (hrun : IsECCARun M V u₀ a s r p) :
    (∀ t₀ T : ℕ, ∑ τ ∈ Finset.Ico t₀ (t₀ + T), ∑ i, p τ i ≤
        M.Pav * T + (M.β * V + M.β * M.Rhat + M.Pmax)) ∧
    limsup (fun T : ℕ => (((T : ℝ)⁻¹ * ∑ τ ∈ Finset.range T, ∑ i, p τ i : ℝ) : EReal)) atTop ≤
      (M.Pav : EReal) := by sorry

end CrossLayerControl.ECCA
