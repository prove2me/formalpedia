-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_queue_bound
-- name    : CrossLayerControl.ECCA.queue_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:35:02.792967+00:00
-- url     : https://prove2.me/theorems/7b2abcf1-93c2-4a3a-b9f8-9b158164132e
-- title:
--   ECCA keeps every data queue below $V+\hat R$ (corrected: $U(0)\le V+\hat R$)
-- statement:
--   Consider the downlink with rates that are nonnegative at every feasible power vector. Let the arrivals satisfy $0\le a_i(t)\le\hat R$, let the initial backlogs satisfy $0\le U_i(0)\le V+\hat R$, and let $(r,p)$ be any run of ECCA with parameter $V$. Then for every slot $t$ and every link $i$,
--   $$0\le U_i(t)\le V+\hat R.$$
--
--   This is the "nature of the flow control algorithm": a queue above $V$ admits nothing, so it never exceeds $V$ by more than one slot's arrivals. It shows that ECCA stabilizes all actual queues deterministically, and it is the first clause of Theorem 6.3.
--
--   Differences from the source:
--   - correction: U(0) unstated → 0 ≤ U_i(0) ≤ V + R̂; reason: with U_i(0) = V + R̂ + 1 the bound U_i(t) ≤ V + R̂ fails at t = 0
--   - generalization: U_i(t) ≤ V + R̂ under the model of §6.3.1 → 0 ≤ U_i(t) ≤ V + R̂, assuming of the model only C_i ≥ 0 at feasible powers, for any real V; reason: adds the lower bound; the argument uses only these facts, and the source's setting satisfies them
--   - generalization: ECCA with the rule admit everything iff U_i(t) ≤ V and a maximizer of (6.14) → any minimizer of the flow-control objective and any maximizer of (6.14) (IsECCARun); reason: ties broken arbitrarily; the paper's run is one of these
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - encoding: A_i(t) ≤ R̂ → 0 ≤ A_i(t) ≤ R̂; reason: arrivals are amounts of data, hence nonnegative; with A_i(t) < 0 the flow-control constraint 0 ≤ R_i(t) ≤ A_i(t) is infeasible and no ECCA run (or admissible decision) exists, so no instance is excluded
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, §6.3.1, p. 115, ¶1, first sentence

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun

namespace CrossLayerControl.ECCA

/-- **ECCA keeps every data queue below V + R̂.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), p. 115, ¶1, first sentence (unnumbered): "From the nature of the
flow control algorithm, we have that Ui(t) ≤ V + R̂ for all i and all t, and hence the above
algorithm trivially stabilizes all actual queues."

If the rates are nonnegative at feasible power vectors, the arrivals satisfy `0 ≤ aᵢ(t) ≤ R̂`, the
initial backlogs satisfy `0 ≤ Uᵢ(0) ≤ V + R̂`, and `(r, p)` is an ECCA run, then for all `t` and `i`,
`0 ≤ Uᵢ(t) ≤ V + R̂`.

**Formalization Note.** The paper does not state `U(0)`; the bound fails at `t = 0` unless
`Uᵢ(0) ≤ V + R̂` (correction C2). ECCA is a relation (`IsECCARun`), so every tie-breaking of the
flow control is covered. Only the nonnegativity of the rates is assumed of the model. -/
theorem queue_bound {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮)
    (hC : ∀ P, IsFeasiblePower M P → ∀ s i, 0 ≤ M.C i P s)
    (V : ℝ) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (ha : ∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) (hrun : IsECCARun M V u₀ a s r p) :
    ∀ t i, 0 ≤ queueU M u₀ s r p t i ∧ queueU M u₀ s r p t i ≤ V + M.Rhat := by sorry

end CrossLayerControl.ECCA
