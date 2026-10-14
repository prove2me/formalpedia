-- Prove2me | Theorems.Thm_ContJRP_Align_claim_3_5_component_sum
-- name    : ContJRP.Align.claim_3_5_component_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:42.931986+00:00
-- url     : https://prove2.me/theorems/b8db2d4d-1295-4567-9bf7-be163e68ad0d
-- title:
--   Claim 3.5, p. 15 — (III) ≤ (1 + ϵ)·N(R*, Δ) + |A*|²·2^{|A*|}
-- statement:
--   Under the standing assumptions below, for every $\Delta\ge0$,
--   $$\text{(III)}=\sum_{C\in\mathrm{CC}(G^*_\Psi)}\Big|\bigcup_{\ell\in C}\mathcal M_{R^*_\ell,\Delta}\Big|\le(1+\epsilon)\cdot N(\mathcal R^*,\Delta)+|\mathcal A^*|^2\cdot2^{|\mathcal A^*|}.$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   The joint orders of the representatives, counted separately per component, exceed their total only by lower-order terms.
--
--   **Formalization Note** Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 15, Claim 3.5 (proof in §4.6, pp. 20–21)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem claim_3_5_component_sum (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∀ Δ : ℝ, 0 ≤ Δ → (termIII ε Tt Tstar Rstar Δ : ℝ) ≤
      (1 + ε) * (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) +
        ((active ε Tt Tstar).card : ℝ) ^ 2 * 2 ^ (active ε Tt Tstar).card := by sorry

end ContJRP.Align
