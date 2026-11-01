-- Prove2me | Theorems.Thm_AssignToSeatRM_lemma_1_dynamic_primal
-- name    : AssignToSeatRM.lemma_1_dynamic_primal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:37.146495+00:00
-- url     : https://prove2.me/theorems/75bc3f21-95e0-4f4c-b2e0-db437e9961e3
-- title:
--   Lemma 1 — with $A=f(C)$, the dynamic primal (14) has the value of LP (2) and an optimal solution satisfying (15)
-- statement:
--   Let $C\in\{0,1\}^{N\times M}$, prices $p_{ij}\ge0$ and demands $d_{ij}\ge0$ (real), and let $A=f(C)$ be the vector of maximal-sequence counts (7). Then
--
--   $$\mathrm{value\ of\ (14)}(A,d)=\mathrm{value\ of\ (2)}(C,d),$$
--
--   and for every itinerary $i^t\le j^t$ the LP (14) has an optimal solution $\gamma$ that also satisfies (15): $\gamma_{u i^t j^t v}\le A_{uv}$ for every $u\le i^t\le j^t\le v$.
--
--   This is what makes RDP well defined and comparable with the hindsight optimum: the maximal-sequence LP, whose size does not grow with the number of seats, loses nothing against the seat-level LP relaxation, and the extra constraints (15), which guarantee that RDP's choice is feasible, do not change its value.
--
--   **Formalization Note** Optimal values are suprema over the feasible sets; "optimal solution" is optimal among all feasible solutions of (14).
--
--   Differences from the source:
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - encoding: legs 1..M, itineraries i ≤ j, C ∈ {0,1}^{N×M} with C_{k0} = C_{k(M+1)} = 0 → natural-number indices with explicit bounds (itins M); C : Fin N → Fin M → Bool read through cap, which is false outside 1..M; reason: Lean convention; same instances
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, Lemma 1, p.20; proof pp.ec16–ec18

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_StaticLP
import Definitions.Def_AssignToSeatRM_DynamicPrimal
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Lemma 1** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, p.20): let `A = f(C)`, where `f` is defined by (7). Then (14) has
the same objective value as (2). Furthermore, for any given `iᵗ ≤ jᵗ`, (14) always has an
optimal solution that satisfies (15).

**Formalization Note.** Stated for every capacity matrix `C`, every real demand vector `d ≥ 0`
(RDP applies the lemma with `d = λ^{[t,T]}`) and nonnegative prices. Optimal values are `sSup`s;
"optimal solution" means optimal among all feasible solutions of (14). -/
theorem lemma_1_dynamic_primal {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ)
    (hp : IsPriceVec M p) (d : ℕ → ℕ → ℝ) (hd : ∀ ij ∈ itins M, 0 ≤ d ij.1 ij.2) :
    lp14Value M p (fun u v => (fC C u v : ℝ)) d = lp2Value C p d ∧
      ∀ ij ∈ itins M, ∃ γ : Idx4 → ℝ,
        IsOptimalOPT M p (fun u v => (fC C u v : ℝ)) d 0 γ ∧
          Sat15 M (fun u v => (fC C u v : ℝ)) ij.1 ij.2 γ := by sorry

end AssignToSeatRM
