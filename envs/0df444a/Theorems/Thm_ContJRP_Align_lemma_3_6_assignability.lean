-- Prove2me | Theorems.Thm_ContJRP_Align_lemma_3_6_assignability
-- name    : ContJRP.Align.lemma_3_6_assignability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:53:05.586011+00:00
-- url     : https://prove2.me/theorems/8c092594-8dbc-41cb-92f0-5a6a3db2e2e4
-- title:
--   Lemma 3.6, p. 15 — C_i(T̂_i) ≤ (1 + 2ϵ)·C_i(T*_i) for every commodity i
-- statement:
--   Under the standing assumptions below, let $K_i,H_i>0$, let $\hat{\mathcal R}$ be a feasible solution of (LP), and let $\hat T$ be a final policy built from it (§2.6): each $\hat T_i$ is one of the representatives $\hat R_\ell$, $\ell\in\mathcal A^*$, or the large interval $\lceil T^{\max}_i\rceil^{(\hat R_1)}$, chosen to minimize $C_i$ among these options. Then for every commodity $i\in[n]$,
--   $$C_i(\hat T_i)\le(1+2\epsilon)\cdot C_i(T^*_i).$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   This is the $2\epsilon$-assignability of the approximate representatives.
--
--   **Formalization Note** Misalignment is not assumed; the page's proof does not use it. Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 15, Lemma 3.6 (proof pp. 15–17)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem lemma_3_6_assignability (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (K H : Fin n → ℝ) (hK : ∀ i, 0 < K i) (hH : ∀ i, 0 < H i)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (That : Fin n → ℝ) (hThat : IsFinalPolicy K H ε Tt Tstar R That) :
    ∀ i, eoqCost (K i) (H i) (That i) ≤ (1 + 2 * ε) * eoqCost (K i) (H i) (Tstar i) := by sorry

end ContJRP.Align
