-- Prove2me | Theorems.Thm_ContJRP_Align_observation_2_2_rep_orders
-- name    : ContJRP.Align.observation_2_2_rep_orders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:41.213583+00:00
-- url     : https://prove2.me/theorems/7a3bfab9-5f2c-4c57-8d5a-529e55cf4417
-- title:
--   Observation 2.2, p. 8 — N(R*, Δ) ≤ N(T*, Δ) for every Δ ≥ 0
-- statement:
--   Under the standing assumptions below, the representatives place no more joint orders than the policy they are drawn from: for every $\Delta\ge0$,
--   $$N(\mathcal R^*,\Delta)\le N(T^*,\Delta).$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   This links the joint orders of the representatives to those of $T^*$ in the density bound (3).
--
--   **Formalization Note** Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 8, Observation 2.2

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem observation_2_2_rep_orders (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∀ Δ : ℝ, 0 ≤ Δ → numOrders (active ε Tt Tstar) Rstar Δ ≤ numOrders Finset.univ Tstar Δ := by sorry

end ContJRP.Align
