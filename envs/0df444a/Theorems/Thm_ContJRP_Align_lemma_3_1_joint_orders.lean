-- Prove2me | Theorems.Thm_ContJRP_Align_lemma_3_1_joint_orders
-- name    : ContJRP.Align.lemma_3_1_joint_orders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:46.892286+00:00
-- url     : https://prove2.me/theorems/5aef9de4-2682-4565-ba95-83e0f6e8e2bb
-- title:
--   Lemma 3.1, p. 12 — N(R̂, Δ) ≤ (1 + 5ϵ)·N(R*, Δ) + 5·|A*|²·2^{|A*|} for every Δ ≥ 0
-- statement:
--   Under the standing assumptions below, let $\hat{\mathcal R}=(\hat R_\ell)_{\ell\in\mathcal A^*}$ be a feasible solution of (LP) whose representatives in different components of $G^*_\Psi$ are misaligned. For every $\Delta\ge0$,
--   $$N(\hat{\mathcal R},\Delta)\le(1+5\epsilon)\cdot N(\mathcal R^*,\Delta)+5\cdot|\mathcal A^*|^2\cdot2^{|\mathcal A^*|}.$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   Dividing by $\Delta$ and letting $\Delta\to\infty$ gives the density bound (3).
--
--   **Formalization Note** Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 12, Lemma 3.1

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem lemma_3_1_joint_orders (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (hmis : CrossMisaligned ε Tt Tstar Rstar R) :
    ∀ Δ : ℝ, 0 ≤ Δ → (numOrders (active ε Tt Tstar) R Δ : ℝ) ≤
      (1 + 5 * ε) * (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) +
        5 * ((active ε Tt Tstar).card : ℝ) ^ 2 * 2 ^ (active ε Tt Tstar).card := by sorry

end ContJRP.Align
