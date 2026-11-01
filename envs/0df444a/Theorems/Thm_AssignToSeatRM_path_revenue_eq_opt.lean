-- Prove2me | Theorems.Thm_AssignToSeatRM_path_revenue_eq_opt
-- name    : AssignToSeatRM.path_revenue_eq_opt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:50.802673+00:00
-- url     : https://prove2.me/theorems/c9387227-4148-428a-96ab-61abd2127137
-- title:
--   Proof of Theorem 4, p.ec19 — the revenue of a decision path is OPT$(A^1,d^{[1,T]},\gamma^{[1,T]})$
-- statement:
--   Fix prices $p_{ij}\ge0$, an initial vector of maximal-sequence counts $A^1$ and a decision path feasible on the periods $1,\dots,T$. Then the total revenue collected along the path equals
--
--   $$\mathrm{OPT}\big(A^1,d^{[1,T]},\gamma^{[1,T]}\big),$$
--
--   the optimal value of (EC.18) with the realized demand $d^{[1,T]}$ and the lower bounds $\gamma^{[1,T]}$ given by the decisions of the path.
--
--   In the proof of Theorem 4 this turns the revenue of RDP on a sample path into a value of the LP family, so that the loss against the hindsight optimum $\mathrm{OPT}(A^1,d^{[1,T]},0)$ telescopes into the increments (EC.19).
--
--   Differences from the source:
--   - generalization: the sample path of RDP from A¹ = f(C¹) → every decision path feasible on [1,T] (each period at most one request; each allocation into a maximal sequence with A^t_{uv} ≥ 1; counts updated by (8)) from every A¹ ∈ ℕ^{u ≤ v}; reason: RDP's path is such a path (constraints (15) give A^t_{uv} ≥ 1 for the chosen [u,v]) and A¹ = f(C¹) is a natural-number vector, so the statement specializes to the source's; the source's proof uses only these properties
--   - encoding: (u^t, i^t, j^t, v^t) for each period, γ^{[t1,t2)}, d^{[t1,t2)}, A^t → dec : ℕ → Option (ℕ⁴) with none = no request and (0,i,j,0) = rejection; gammaCount, demandCount count periods in [t1,t2); msState gives A^t; reason: Lean convention; same paths
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, proof of Theorem 4, p.ec19 (first paragraph)

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_DynamicPrimal
import Definitions.Def_AssignToSeatRM_DecisionPath
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Proof of Theorem 4, p.ec19** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188): "From Lemma EC.3, by setting `d̂ = 0` and `t₁ = t₂ = T + 1`, we can
see that the total revenue collected under ω is `OPT(A¹, d^{[1,T]}, γ^{[1,T]})`."

**Formalization Note.** Stated for every horizon `T`, every `A¹ ∈ ℕ^{u ≤ v}` and every decision
path feasible on `[1, T]`, of which RDP's path is one. `d^{[1,T]} = d^{[1,T+1)}`,
`γ^{[1,T]} = γ^{[1,T+1)}`. Prices are nonnegative. -/
theorem path_revenue_eq_opt {M T : ℕ} (p : ℕ → ℕ → ℝ) (hp : IsPriceVec M p)
    (A₁ : ℕ → ℕ → ℕ) (dec : ℕ → Option Idx4) (hdec : IsFeasPath M T A₁ dec) :
    pathRevenue p dec T =
      OPT M p (fun u v => (A₁ u v : ℝ)) (fun i j => (demandCount dec 1 (T + 1) i j : ℝ))
        (fun c => (gammaCount dec 1 (T + 1) c : ℝ)) := by sorry

end AssignToSeatRM
