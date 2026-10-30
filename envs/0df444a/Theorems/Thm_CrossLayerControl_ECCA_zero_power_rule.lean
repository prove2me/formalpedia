-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_zero_power_rule
-- name    : CrossLayerControl.ECCA.zero_power_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:35:52.553718+00:00
-- url     : https://prove2.me/theorems/f50daa72-573a-4323-8f55-47489b60c957
-- title:
--   ECCA allocates zero power when $D(t)>U_i(t)\beta$ (corrected: no beneficial cross-coupling of rates)
-- statement:
--   Assume the standing hypotheses of Theorem 6.3: the signs, the rate bound (3.4), the $\beta$-condition
--   $$C_i(P,s)\le C_i(P[i],s)+\beta P_i,$$
--   and cross-monotonicity $C_j(P,s)\le C_j(P[i],s)$ for $j\neq i$, all at feasible power vectors $P$. Let the initial backlogs be nonnegative and let $(r,p)$ be any ECCA run. Then for every slot $t$ and link $i$,
--   $$D(t)>U_i(t)\,\beta\ \Longrightarrow\ P_i(t)=0.$$
--
--   The power allocation (6.14) switches off a link whose backlog is small relative to the virtual power queue. This is the step from which the bound on $D(t)$ follows.
--
--   Differences from the source:
--   - correction: β-condition only → β-condition plus cross-monotonicity C_j(P,s) ≤ C_j(P[i],s) for j ≠ i (DownlinkHyp); reason: the printed claim is false: L = 2, Pmax = 1, Pav = 0.5, β = 0.01, V = 10, R̂ = 1, µmax = 1, C_1 ≡ 0, C_2(P) = 1[P_1 ≥ 1], A ≡ (0,1) satisfies every printed assumption, ECCA allocates P = (1,0) with D(t) > βU_1(t), and D(t) reaches 10 > βV + βR̂ + Pmax = 1.11
--   - reading: U(0) unstated → U_i(0) ≥ 0; reason: backlogs are nonnegative
--   - reading: signs of Pav, Pmax, R̂ unstated → 0 ≤ Pav, 0 ≤ Pmax, 0 ≤ R̂ (RateHyp); reason: a negative average power budget is unsatisfiable; R̂ ≥ 0 is forced by 0 ≤ A_i ≤ R̂ when L ≥ 1 and keeps L = 0 nondegenerate; Pmax ≥ 0 follows from 0 ≤ Pav < Pmax
--   - generalization: ECCA with the rule admit everything iff U_i(t) ≤ V and a maximizer of (6.14) → any minimizer of the flow-control objective and any maximizer of (6.14) (IsECCARun); reason: ties broken arbitrarily; the paper's run is one of these
--   - generalization: β-condition for every P with Σ P_i ≤ Pmax; V > 0 → β-condition only at feasible (nonnegative) P; V any real; reason: weaker hypotheses; the source's instances satisfy them
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, §6.3.1, p. 115, ¶1, last two sentences

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun

namespace CrossLayerControl.ECCA

/-- **ECCA allocates zero power to a link whose backlog is small relative to D(t).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), p. 115, ¶1 (unnumbered): "Specifically, assume there exists a
constant β > 0 such that for any link i, any topology state S(t), and any power vector P such that
Σi Pi ≤ Pmax, we have: Ci(P,S(t)) ≤ Ci(P[i],S(t)) + βPi, where P = (P1,...,PL), and P[i] is equal
to P with the exception that the ith entry is set to zero. It follows that if D(t) > Ui(t)β, then
Pi(t) = 0."

Under the standing assumptions `DownlinkHyp M` (which include the β-condition and
cross-monotonicity), nonnegative initial backlogs and an ECCA run, for all `t` and `i`:
if `D(t) > Uᵢ(t) β` then `Pᵢ(t) = 0`.

**Formalization Note (correction C1).** The page's derivation from the β-condition alone is false:
with `C₁ ≡ 0`, `C₂(P) = 1[P₁ ≥ 1]`, `Pmax = 1`, the power vector `(1, 0)` is the unique maximizer of
(6.14) whenever `U₂ > D > 0 = βU₁`. `DownlinkHyp` therefore also assumes that zeroing the power of
link `i` does not lower any other link's rate. -/
theorem zero_power_rule {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : DownlinkHyp M)
    (V : ℝ) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (hrun : IsECCARun M V u₀ a s r p) :
    ∀ t i, queueU M u₀ s r p t i * M.β < virtD M p t → p t i = 0 := by sorry

end CrossLayerControl.ECCA
