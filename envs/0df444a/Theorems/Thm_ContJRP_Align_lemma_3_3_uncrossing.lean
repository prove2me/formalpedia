-- Prove2me | Theorems.Thm_ContJRP_Align_lemma_3_3_uncrossing
-- name    : ContJRP.Align.lemma_3_3_uncrossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:46.956985+00:00
-- url     : https://prove2.me/theorems/61f465ba-8765-4f14-9de3-5cb9145f2aea
-- title:
--   Lemma 3.3, p. 14 — (I) ≤ (1 + 4ϵ)·N(R*, Δ) + 4·|A*|²·2^{|A*|}
-- statement:
--   Under the standing assumptions below, let $\hat{\mathcal R}$ be a feasible solution of (LP). For every $\Delta\ge0$, the uncrossing term of (4) satisfies
--   $$\text{(I)}\le(1+4\epsilon)\cdot N(\mathcal R^*,\Delta)+4\cdot|\mathcal A^*|^2\cdot2^{|\mathcal A^*|}.$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   Together with Lemma 3.2 this bounds the joint orders of $\hat{\mathcal R}$.
--
--   **Formalization Note** (I) is the signed sum over nonempty uncrossing $\mathcal A\subseteq\mathcal A^*$, computed for $\hat{\mathcal R}$. Misalignment is not assumed; the page's proof does not use it. Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 14, Lemma 3.3

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem lemma_3_3_uncrossing (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R) :
    ∀ Δ : ℝ, 0 ≤ Δ → ((termI ε Tt Tstar Rstar R Δ : ℤ) : ℝ) ≤
      (1 + 4 * ε) * (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) +
        4 * ((active ε Tt Tstar).card : ℝ) ^ 2 * 2 ^ (active ε Tt Tstar).card := by sorry

end ContJRP.Align
