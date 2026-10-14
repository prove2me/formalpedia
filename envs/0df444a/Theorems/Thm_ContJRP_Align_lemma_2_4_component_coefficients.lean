-- Prove2me | Theorems.Thm_ContJRP_Align_lemma_2_4_component_coefficients
-- name    : ContJRP.Align.lemma_2_4_component_coefficients
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:36.763087+00:00
-- url     : https://prove2.me/theorems/fa36e2c8-d389-40f9-82d3-06fa3bfb551d
-- title:
--   Lemma 2.4, p. 10 — on each component C, every (LP_C) solution has R_ℓ = β_ℓ R_{σ_C} with β_ℓ = β⁺_ℓ/β⁻_ℓ, β^± ≤ Ψ^{|C|}
-- statement:
--   Under the standing assumptions below, let $C\in\mathrm{CC}(G^*_\Psi)$ be a connected component of the alignment graph and $\sigma_C\in C$ any vertex of it. There exist coefficients $\{\beta_\ell\}_{\ell\in C}$ such that
--
--   1. in any feasible solution of (LP$_C$), $R_\ell=\beta_\ell\cdot R_{\sigma_C}$ for every $\ell\in C$;
--   2. for every $\ell\in C$, $\beta_\ell=\beta^+_\ell/\beta^-_\ell$ where $\beta^+_\ell,\beta^-_\ell$ are positive integers with
--   $$\beta^+_\ell,\ \beta^-_\ell\le\Psi^{|C|}.$$
--
--   **Standing assumptions.** Throughout, $\epsilon\in(0,\tfrac12)$; $T^*=(T^*_1,\dots,T^*_n)$ is a policy with $n\ge1$ and all $T^*_i>0$, $T^*_{\min}=\min_i T^*_i$; $\tilde T_{\min}$ satisfies (2), $(1-\epsilon/2)\,T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$; and $\mathcal R^*=\{R^*_\ell\}_{\ell\in\mathcal A^*}$ is any choice of representatives, $R^*_\ell$ being some $T^*_i$ in the active segment $S_\ell$.
--
--   So each single-component program is a one-variable problem in $R_{\sigma_C}$.
--
--   **Formalization Note** The page says "integers bounded by $\Psi^{|C|}$"; they are taken positive. The time bound for computing the coefficients is not formalized. Segments are 0-indexed in Lean (the paper's $S_\ell$ is Lean index $\ell-1$, so $R_1$ is `R 0`). The statement is proved for every positive reference policy $T^*$, not only an optimal one, and does not assume the difficult regime $T^*_{\min}<(n/\epsilon)K_0/\widetilde{\mathrm{OPT}}$: the page's argument uses only (2).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 10, Lemma 2.4 (proof in §4.3, p. 19)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem lemma_2_4_component_coefficients (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∀ C ∈ components ε Tt Tstar Rstar, ∀ σ ∈ C, ∃ β : ℕ → ℝ,
      (∀ R : ℕ → ℝ, IsLPFeasibleOn ε Tt Tstar Rstar C R → ∀ ℓ ∈ C, R ℓ = β ℓ * R σ) ∧
      ∀ ℓ ∈ C, ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) ≤ Psi ε ^ C.card ∧ (q : ℝ) ≤ Psi ε ^ C.card ∧
        β ℓ = (p : ℝ) / q := by sorry

end ContJRP.Align
