-- Prove2me | Theorems.Thm_ContJRP_Align_corollary_2_6_scaling
-- name    : ContJRP.Align.corollary_2_6_scaling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:38.716145+00:00
-- url     : https://prove2.me/theorems/34693db6-361a-4fd8-8f8c-214dbd6ec9ad
-- title:
--   Corollary 2.6, p. 11 — on each component C, every feasible R satisfies R_ℓ = γ_{C,R} R*_ℓ with γ_{C,R} ∈ 1 ± ϵ
-- statement:
--   Under the standing assumptions below, for every feasible solution $(R_\ell)_{\ell\in\mathcal A^*}$ of (LP) and every component $C\in\mathrm{CC}(G^*_\Psi)$ there is a coefficient $\gamma_{C,R}$ with
--   $$1-\epsilon\le\gamma_{C,R}\le1+\epsilon\qquad\text{and}\qquad R_\ell=\gamma_{C,R}\cdot R^*_\ell\ \text{ for every }\ell\in C.$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   On each component the approximate representatives are thus a common rescaling of the optimal ones, which is what lets their common multiples be compared in §3.
--
--   **Formalization Note** Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 11, Corollary 2.6

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem corollary_2_6_scaling (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∀ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R → ∀ C ∈ components ε Tt Tstar Rstar,
      ∃ γ : ℝ, 1 - ε ≤ γ ∧ γ ≤ 1 + ε ∧ ∀ ℓ ∈ C, R ℓ = γ * Rstar ℓ := by sorry

end ContJRP.Align
