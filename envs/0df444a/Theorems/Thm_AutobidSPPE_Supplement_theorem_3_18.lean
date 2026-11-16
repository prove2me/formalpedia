-- Prove2me | Theorems.Thm_AutobidSPPE_Supplement_theorem_3_18
-- name    : AutobidSPPE.Supplement.theorem_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:06:21.514204+00:00
-- url     : https://prove2.me/theorems/c481263c-aa2e-4663-b19b-2181112ce4f2
-- title:
--   Theorem 3.18 — a direct triangular budget regime
-- statement:
--   Let $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with arbitrary $\bar v_i>0$, and budgets $\rho_i>0$. With $C_j=\max_{S\subseteq[n]\setminus\{j\}}c_j(S)$, suppose $\rho_j\ge C_j$ for all but at most one bidder $i$ (whose budget $\rho_i>0$ is arbitrary). Then the iteration (51) has a unique SPTE $\alpha^*$, and for every fixed $0<\tau_j\le1$ it converges geometrically to $\alpha^*$ from every initialization in $[0,1]^n$.
--
--   No spending P-matrix certificate is required.
--
--   **Formalization Note** "All but at most one bidder" is: there is a bidder $i$ such that $\rho_j\ge C_j$ for every $j\ne i$.
--
--   Differences from the source:
--   - generalization: the smallest index wins a tie (§3.2, p.26) → every deterministic single-winner tie rule (AutobidSPPE.TieRule); reason: under independent uniform values ties between values have probability zero, so spending, loss, response and equilibria do not depend on the rule; the smallest-index rule is one instance
--   - reading: globally geometric convergence → ∃ C, q ∈ (0,1) with ‖α^(t) − α*‖ ≤ C q^t for all t and all starts in [0,1]^n; reason: constants uniform in the start, the stronger reading, which the proofs give
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.18, p.40

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_IsBayesianSPTE
import Definitions.Def_AutobidSPPE_Supplement_residualT
import Definitions.Def_AutobidSPPE_Supplement_iterateT
import Definitions.Def_AutobidSPPE_Supplement_coefMax

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Theorem 3.18, p.40 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), a direct triangular budget regime. Let `n ≥ 2`, `vᵢ ∼ Unif[0, v̄ᵢ]` independently
with arbitrary `v̄ᵢ > 0`, and `ρᵢ > 0`. Suppose `ρⱼ ≥ Cⱼ = max_{S ⊆ [n]∖{j}} cⱼ(S)` for all but at most one
bidder `i` (the remaining budget `ρᵢ > 0` is arbitrary). Then the iteration (51) has a unique SPTE `α*`, and for
every fixed `0 < τⱼ ≤ 1` it converges geometrically to `α*` from every initialization in `[0,1]ⁿ`.

**Formalization Note** "All but at most one bidder" is `∃ i, ∀ j ≠ i` (this covers the case of no exception).
"Converges geometrically" is: there are `C` and `q ∈ (0,1)`, uniform in the start, with
`‖α⁽ᵗ⁾ − α*‖ ≤ C qᵗ` for every `t ≥ 0`. `‖·‖` is the sup norm. Every tie rule is allowed. -/
theorem theorem_3_18 {n : ℕ} (hn : 2 ≤ n) (vbar ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i)
    (hρ : ∀ i, 0 < ρ i) (tie : TieRule n) (hbud : ∃ i, ∀ j, j ≠ i → coefMax vbar j ≤ ρ j) :
    ∃ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar ∧
      (∀ β, IsBayesianSPTE vbar ρ tie β → β = αstar) ∧
      ∀ τ : Fin n → ℝ, (∀ j, 0 < τ j ∧ τ j ≤ 1) →
        ∃ C q : ℝ, 0 < q ∧ q < 1 ∧ ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
          ∀ t : ℕ, ‖iterateT vbar ρ tie τ α0 t - αstar‖ ≤ C * q ^ t := by sorry

end AutobidSPPE.Supplement
