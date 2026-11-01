-- Prove2me | Theorems.Thm_AssignToSeatRM_lemma_ec5_stability
-- name    : AssignToSeatRM.lemma_ec5_stability
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:31.363307+00:00
-- url     : https://prove2.me/theorems/a5989faa-bde3-4bfc-9fa5-0e2b5cea7d1f
-- title:
--   Lemma EC.5 — optimal solutions of (14) are Lipschitz in the demand, with a constant depending only on the constraint matrix
-- statement:
--   Fix the number of legs $M$. There is $\delta>0$, depending only on the constraint matrix of (14) (which is determined by $M$), such that for all prices $p_{ij}\ge0$, all right-hand sides $A\ge0$ (real; in the paper $A=A^t=f(C^t)$) and all demands $d,\tilde d\ge0$: for every optimal solution $\gamma^{*}$ of $\mathrm{OPT}(A,d,0)$ there is an optimal solution $\tilde\gamma^{*}$ of $\mathrm{OPT}(A,\tilde d,0)$ with
--
--   $$\|\gamma^{*}-\tilde\gamma^{*}\|_\infty\ \le\ \delta\,\|d-\tilde d\|_\infty.$$
--
--   This is a special case of the Lipschitz continuity of LP solution sets in the right-hand side (Mangasarian and Shiau 1987, Theorem 2.4). In the proof of Theorem 4 it compares RDP's solution, computed with expected demand, with the optimal solution for the realized demand.
--
--   **Formalization Note** The sup-norm of $\gamma$ runs over all variables of (14), rejections included; that of $d$ over all itineraries.
--
--   Differences from the source:
--   - encoding: δ 'only depends on the constraint matrix of (14), and independent of A^t, d ≥ 0' → ∃ δ > 0 after M, before p, A, d, d̃; reason: the constraint matrix of (14) is determined by M
--   - generalization: A^t = f(C^t) (the printed text reads 'independent of A^t, d ≥ 0') → any real vector A ≥ 0; reason: (EC.18) takes A non-negative and f(C^t) is such a vector, so the statement specializes to the source's; Mangasarian and Shiau's Theorem 2.4 covers every right-hand side
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, Lemma EC.5, p.ec21

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_DynamicPrimal
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Lemma EC.5** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, p.ec21; a special case of Mangasarian and Shiau 1987, Theorem 2.4):
there exists some `δ > 0` that only depends on the constraint matrix of (14), and independent of
`Aᵗ`, `d ≥ 0`, such that for any optimal solution `γ^{*,t}` of `OPT(Aᵗ, d, 0)`, there exists an
optimal solution `γ̃^{*,t}` of `OPT(Aᵗ, d̃, 0)` with `‖γ^{*,t} − γ̃^{*,t}‖_∞ ≤ δ‖d − d̃‖_∞`.

**Formalization Note.** The constraint matrix of (14) is determined by the number of legs `M`,
so `δ` is chosen after `M` and before the prices `p ≥ 0`, the right-hand sides `A ≥ 0` (real, as
in (EC.18); `Aᵗ = f(Cᵗ)` is a special case) and the demands `d, d̃ ≥ 0`. The sup-norms run over all
variables of (14) (rejections included) and over all itineraries. -/
theorem lemma_ec5_stability (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (p : ℕ → ℕ → ℝ), IsPriceVec M p → ∀ (A d d' : ℕ → ℕ → ℝ),
        (∀ uv ∈ itins M, 0 ≤ A uv.1 uv.2) →
        (∀ ij ∈ itins M, 0 ≤ d ij.1 ij.2) → (∀ ij ∈ itins M, 0 ≤ d' ij.1 ij.2) →
        ∀ γ : Idx4 → ℝ, IsOptimalOPT M p A d 0 γ →
          ∃ γ' : Idx4 → ℝ, IsOptimalOPT M p A d' 0 γ' ∧
            supNormOn (gammaIdx M) (fun c => γ c - γ' c) ≤
              δ * supNormOn (itins M) (fun ij => d ij.1 ij.2 - d' ij.1 ij.2) := by sorry

end AssignToSeatRM
