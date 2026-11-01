-- Prove2me | Theorems.Thm_AssignToSeatRM_supported_choice_no_loss
-- name    : AssignToSeatRM.supported_choice_no_loss
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:57.772902+00:00
-- url     : https://prove2.me/theorems/0fb7684b-83cf-44da-a4ce-6d1e4ffebcce
-- title:
--   Proof of Theorem 4, p.ec23 — if the optimal $\gamma^*$ puts at least one unit on the chosen option, committing to it loses nothing
-- statement:
--   Let $A\in\mathbb N^{\{u\le v\}}$ be maximal-sequence counts, $d\ge0$ demands, $p_{ij}\ge0$ prices, and let $\gamma^*$ be an optimal solution of $\mathrm{OPT}(A,d,0)$, the dynamic primal (14). Let $o$ be a variable of (14) — an allocation $(u,i,j,v)$ or a rejection $(0,i,j,0)$ — with $\gamma^*_o\ge1$. Then
--
--   $$\mathrm{OPT}(A,d,e_o)=\mathrm{OPT}(A,d,0),$$
--
--   where $e_o$ is the indicator of $o$: imposing the lower bound $\gamma_o\ge1$ (one request handled as $o$) does not lower the optimal value, since $\gamma^*$ stays feasible.
--
--   In the proof of Theorem 4 this shows that a period's increment of the loss decomposition can be positive only if the optimal solution for the realized demand has $\gamma^{*,t}_{u^ti^tj^tv^t}<1$, which is (EC.27).
--
--   Differences from the source:
--   - generalization: A^t = f(C^t), d = d^{[t,θT]}, γ^{*,t} optimal for OPT(A^t, d^{[t,θT]}, 0), o = RDP's choice (u^t,i^t,j^t,v^t) → any A ∈ ℕ^{u≤v}, any d ≥ 0, any optimal γ* of OPT(A, d, 0), any variable o of (14) with γ*_o ≥ 1; reason: the source's objects are such A, d, γ*, o; the argument uses only optimality of γ* and γ*_o ≥ 1
--   - encoding: γ^{[t,t+1)} (the decision of period t) → Pi.single o 1; reason: one decision is the indicator of its index
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, proof of Theorem 4, p.ec23 (reason for (EC.27))

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_DynamicPrimal
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Proof of Theorem 4, p.ec23** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188), the reason for (EC.27): "If `γ^{*,t}_{uᵗiᵗjᵗvᵗ} ≥ 1`, then
`γ^{*,t}` is still feasible for `OPT(Aᵗ, d^{[t,θT]}, γ^{[t,t+1)})`, so `OPT(Aᵗ, d^{[t,θT]}, 0)` and
`OPT(Aᵗ, d^{[t,θT]}, γ^{[t,t+1)})` must be equal."

**Formalization Note.** Stated for any counts `A ∈ ℕ^{u ≤ v}`, any demands `d ≥ 0`, any optimal
solution `γ*` of `OPT(A, d, 0)` and any variable `o = (u, i, j, v)` of (14) (a rejection
`(0, i, j, 0)` included) with `γ*_o ≥ 1`; `γ^{[t,t+1)}` is the indicator `e_o` of `o`. -/
theorem supported_choice_no_loss {M : ℕ} (p : ℕ → ℕ → ℝ) (hp : IsPriceVec M p)
    (A : ℕ → ℕ → ℕ) (d : ℕ → ℕ → ℝ) (hd : ∀ ij ∈ itins M, 0 ≤ d ij.1 ij.2)
    (γ : Idx4 → ℝ) (hγ : IsOptimalOPT M p (fun u v => (A u v : ℝ)) d 0 γ)
    (o : Idx4) (ho : o ∈ gammaIdx M) (h1 : 1 ≤ γ o) :
    OPT M p (fun u v => (A u v : ℝ)) d (Pi.single o 1) =
      OPT M p (fun u v => (A u v : ℝ)) d 0 := by sorry

end AssignToSeatRM
