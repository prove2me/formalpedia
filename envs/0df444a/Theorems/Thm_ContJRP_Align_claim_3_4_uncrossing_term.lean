-- Prove2me | Theorems.Thm_ContJRP_Align_claim_3_4_uncrossing_term
-- name    : ContJRP.Align.claim_3_4_uncrossing_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:29.030278+00:00
-- url     : https://prove2.me/theorems/c5b7ec78-3cc8-4055-9b2f-065c28408439
-- title:
--   Claim 3.4, p. 14 — |⋂_{ℓ∈A} M_{R̂_ℓ,Δ}| ∈ (1/γ_{C,R̂})·|⋂_{ℓ∈A} M_{R*_ℓ,Δ}| ± 2
-- statement:
--   Under the standing assumptions below, let $\hat{\mathcal R}$ be a feasible solution of (LP), $C\in\mathrm{CC}(G^*_\Psi)$ a component, and $\gamma$ a coefficient with $1-\epsilon\le\gamma\le1+\epsilon$ and $\hat R_\ell=\gamma R^*_\ell$ for all $\ell\in C$ (Corollary 2.6). For every nonempty $\mathcal A\subseteq C$ and every $\Delta\ge0$,
--   $$\Big|\,\Big|\bigcap_{\ell\in\mathcal A}\mathcal M_{\hat R_\ell,\Delta}\Big|-\frac1\gamma\Big|\bigcap_{\ell\in\mathcal A}\mathcal M_{R^*_\ell,\Delta}\Big|\,\Big|\le2 .$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   This compares each uncrossing term of $\hat{\mathcal R}$ with the corresponding term of $\mathcal R^*$.
--
--   **Formalization Note** The page's "$\in\frac1\gamma x\pm2$" is written as a two-sided absolute-value bound. Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 14, Claim 3.4 (proof in §4.5, p. 20)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem claim_3_4_uncrossing_term (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (C : Finset ℕ) (hC : C ∈ components ε Tt Tstar Rstar)
    (γ : ℝ) (hγ1 : 1 - ε ≤ γ) (hγ2 : γ ≤ 1 + ε) (hγ : ∀ ℓ ∈ C, R ℓ = γ * Rstar ℓ)
    (A : Finset ℕ) (hA : A ⊆ C) (hAne : A.Nonempty) :
    ∀ Δ : ℝ, 0 ≤ Δ → |((interMultiples A R Δ).card : ℝ) -
      ((interMultiples A Rstar Δ).card : ℝ) / γ| ≤ 2 := by sorry

end ContJRP.Align
