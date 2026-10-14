-- Prove2me | Theorems.Thm_ContJRP_Align_eq_3_density
-- name    : ContJRP.Align.eq_3_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:35.142212+00:00
-- url     : https://prove2.me/theorems/88a9f066-07c7-4950-8c82-7b96a087f7c7
-- title:
--   (3), p. 12 — lim N(R̂,Δ)/Δ ≤ (1 + 5ϵ)·lim N(T*,Δ)/Δ
-- statement:
--   Under the standing assumptions below, let $\hat{\mathcal R}$ be a feasible solution of (LP) whose representatives in different components of $G^*_\Psi$ are misaligned. Both ordering densities exist and
--   $$\lim_{\Delta\to\infty}\frac{N(\hat{\mathcal R},\Delta)}{\Delta}\le(1+5\epsilon)\cdot\lim_{\Delta\to\infty}\frac{N(T^*,\Delta)}{\Delta}.\qquad(3)$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   By (1) this says the joint orders placed by the final policy cost at most $(1+5\epsilon)J(T^*)$.
--
--   **Formalization Note** The statement asserts that both limits exist (as `Tendsto`) and compares their values, so it does not depend on the value `limUnder` takes when a limit fails to exist. Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 12, inequality (3)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem eq_3_density (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (hmis : CrossMisaligned ε Tt Tstar Rstar R) :
    ∃ dR dT : ℝ,
      Filter.Tendsto (fun Δ : ℝ => (numOrders (active ε Tt Tstar) R Δ : ℝ) / Δ) Filter.atTop (nhds dR) ∧
      Filter.Tendsto (fun Δ : ℝ => (numOrders Finset.univ Tstar Δ : ℝ) / Δ) Filter.atTop
        (nhds dT) ∧
      dR ≤ (1 + 5 * ε) * dT := by sorry

end ContJRP.Align
