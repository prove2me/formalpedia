-- Prove2me | Theorems.Thm_ContJRP_Align_lemma_2_5_misaligned_solution
-- name    : ContJRP.Align.lemma_2_5_misaligned_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:26.235235+00:00
-- url     : https://prove2.me/theorems/08d0d38b-bc31-4c05-b8ae-91d8307f4c49
-- title:
--   Lemma 2.5, p. 11 — (LP) has a feasible solution in which representatives of different components are misaligned
-- statement:
--   Under the standing assumptions below, there is a feasible solution $(R_\ell)_{\ell\in\mathcal A^*}$ of (LP) in which every pair of representatives belonging to different components of $G^*_\Psi$ is misaligned: $\alpha_1R_{\ell_1}\ne\alpha_2R_{\ell_2}$ for all positive integers $\alpha_1,\alpha_2\le\Psi$.
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   These are the solutions from which the final policy is built; the bound on its cost (Theorem 1.3) is proved for every such solution.
--
--   **Formalization Note** Only the existence half is formalized; the running time $O(2^{O(\frac1\epsilon\log\frac1\epsilon)})$ of the construction is not. In this existence form the optimal representatives $R^*$ are themselves a witness (pairs in different components are by definition not $\Psi$-aligned); the paper's content is a construction that does not know $R^*$. Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 11, Lemma 2.5 (proof in §4.4, pp. 19–20)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem lemma_2_5_misaligned_solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∃ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R ∧ CrossMisaligned ε Tt Tstar Rstar R := by sorry

end ContJRP.Align
