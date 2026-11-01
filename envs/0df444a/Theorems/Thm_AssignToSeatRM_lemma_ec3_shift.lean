-- Prove2me | Theorems.Thm_AssignToSeatRM_lemma_ec3_shift
-- name    : AssignToSeatRM.lemma_ec3_shift
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:50.377668+00:00
-- url     : https://prove2.me/theorems/29ac8984-d2ec-47dc-8d13-9a71a4876c6c
-- title:
--   Lemma EC.3 — shifting OPT$(A,d,\hat\gamma)$ along a decision path
-- statement:
--   Fix prices $p_{ij}\ge0$, an initial vector of maximal-sequence counts $A^1$, and a decision path that is feasible on the periods $1,\dots,T$ (at most one request per period; every allocation into $[u,v]$ uses an existing maximal sequence; $A^t$ evolves by (8)). Fix nonnegative $\hat d=\{\hat d_{ij}\}$. Then for every $1\le t_1\le t_2\le T+1$,
--
--   $$\mathrm{OPT}\big(A^1,\hat d+d^{[1,t_2)},\gamma^{[1,t_2)}\big)=\sum_{i\le j}p_{ij}\sum_{(u,v):\,u\le i\le j\le v}\gamma^{[1,t_1)}_{uijv}+\mathrm{OPT}\big(A^{t_1},\hat d+d^{[t_1,t_2)},\gamma^{[t_1,t_2)}\big).$$
--
--   Here $\mathrm{OPT}(A,d,\hat\gamma)$ is the optimal value of (EC.18), the dynamic primal (14) with lower bounds $\gamma\ge\hat\gamma$, and $d^{[t_1,t_2)}$, $\gamma^{[t_1,t_2)}$ count the requests and decisions of the periods in $[t_1,t_2)$.
--
--   The identity lets the proof of Theorem 4 compare, period by period, the revenue already collected with the best completion in hindsight.
--
--   Differences from the source:
--   - generalization: the sample path of RDP from A¹ = f(C¹) → every decision path feasible on [1,T] (each period at most one request; each allocation into a maximal sequence with A^t_{uv} ≥ 1; counts updated by (8)) from every A¹ ∈ ℕ^{u ≤ v}; reason: RDP's path is such a path (constraints (15) give A^t_{uv} ≥ 1 for the chosen [u,v]) and A¹ = f(C¹) is a natural-number vector, so the statement specializes to the source's; the source's proof uses only these properties
--   - encoding: (u^t, i^t, j^t, v^t) for each period, γ^{[t1,t2)}, d^{[t1,t2)}, A^t → dec : ℕ → Option (ℕ⁴) with none = no request and (0,i,j,0) = rejection; gammaCount, demandCount count periods in [t1,t2); msState gives A^t; reason: Lean convention; same paths
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, Lemma EC.3, p.ec18; (EC.18) p.ec18

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

/-- **Lemma EC.3** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, p.ec18): fix any nonnegative `d̂ = {d̂_{ij}}`. For any
`1 ≤ t₁ ≤ t₂ ≤ T + 1`,
`OPT(A¹, d̂ + d^{[1,t₂)}, γ^{[1,t₂)}) = Σ_{i ≤ j} p_{ij} Σ_{(u,v)} γ^{[1,t₁)}_{uijv}
  + OPT(A^{t₁}, d̂ + d^{[t₁,t₂)}, γ^{[t₁,t₂)})`.

**Formalization Note.** Stated for every horizon `T`, every initial vector of maximal-sequence
counts `A¹ ∈ ℕ^{u ≤ v}` and every decision path feasible on `[1, T]` (each allocation goes into
an existing maximal sequence; at most one request per period), of which RDP's path is one.
`A^t` follows (8). Prices are nonnegative. -/
theorem lemma_ec3_shift {M T : ℕ} (p : ℕ → ℕ → ℝ) (hp : IsPriceVec M p)
    (A₁ : ℕ → ℕ → ℕ) (dec : ℕ → Option Idx4) (hdec : IsFeasPath M T A₁ dec)
    (dhat : ℕ → ℕ → ℝ) (hdhat : ∀ ij ∈ itins M, 0 ≤ dhat ij.1 ij.2)
    (t₁ t₂ : ℕ) (h₁ : 1 ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ T + 1) :
    OPT M p (fun u v => (A₁ u v : ℝ)) (fun i j => dhat i j + (demandCount dec 1 t₂ i j : ℝ))
        (fun c => (gammaCount dec 1 t₂ c : ℝ)) =
      dpObjective M p (fun c => (gammaCount dec 1 t₁ c : ℝ)) +
        OPT M p (fun u v => (msState A₁ dec t₁ u v : ℝ))
          (fun i j => dhat i j + (demandCount dec t₁ t₂ i j : ℝ))
          (fun c => (gammaCount dec t₁ t₂ c : ℝ)) := by sorry

end AssignToSeatRM
