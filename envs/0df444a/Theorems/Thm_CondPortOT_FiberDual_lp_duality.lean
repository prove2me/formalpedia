-- Prove2me | Theorems.Thm_CondPortOT_FiberDual_lp_duality
-- name    : CondPortOT.FiberDual.lp_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:27.331849+00:00
-- url     : https://prove2.me/theorems/5a7bf41b-03e3-40c5-a9cf-197292f71ab8
-- title:
--   (29), p. 51 — LP duality: the sup over (υ, t) ∈ Υ, θ ∈ Q(υ, t) equals the inf of ϕ + (Nε)⁻¹ν⁺ − N⁻¹ν⁻ over 𝒱
-- statement:
--   Let $N\ge1$, $d\in\mathbb R^N$, $\mathcal I_1\subseteq[N]$ with complement $\mathcal I_2$, $\rho\in\mathbb R$, $\varepsilon>0$, $\lambda\in\mathbb R^N_+$ and $s\in\mathbb R^N$. Let
--   $$\Upsilon=\Big\{(\upsilon,t)\in[0,1]^N\times\mathbb R:\ \upsilon_i\le t\ \forall i,\ \sum_{i\in[N]}\upsilon_i=1,\ N^{-1}\le t\le(N\varepsilon)^{-1}\Big\},$$
--   $$\mathcal Q(\upsilon,t)=\Big\{\theta\in\mathbb R^N_+:\ \sum_{i\in\mathcal I_1}\big(\theta_i+(t-\upsilon_i)d_i\big)+\sum_{i\in\mathcal I_2}\big(\theta_i+\upsilon_id_i\big)\le N\rho t\Big\}.$$
--   If some $(\upsilon,t)\in\Upsilon$ and $\theta\in\mathcal Q(\upsilon,t)$ exist, then
--   $$\sup_{(\upsilon,t)\in\Upsilon}\ \sup_{\theta\in\mathcal Q(\upsilon,t)}\ \sum_{i\in[N]}\theta_i\lambda_i+\upsilon_is_i=\inf\Big\{\phi+(N\varepsilon)^{-1}\nu^+-N^{-1}\nu^-:\ (\lambda,s,\nu^+,\nu^-,\phi,\varphi,\psi)\in\mathcal V\Big\},$$
--   where $\mathcal V$ is the dual set (16) built from these $d$, $\mathcal I_1$ and $\rho$, with $\lambda$ and $s$ held fixed, and the infimum ranges over $\nu^\pm\ge0$, $\phi\in\mathbb R$, $\varphi\ge0$, $\psi\in\mathbb R^N_+$.
--
--   This is the linear-programming duality that turns the inner two suprema of (28) into the dual program (29), whence the set $\mathcal V$ of Theorem 4.4.
--
--   **Formalization Note.** Both sides are computed in the extended reals. The paper justifies strong duality by $\rho>\rho_{\min}$; here that is replaced by the direct feasibility hypothesis on $(\upsilon,t,\theta)$, so the statement is pure linear programming.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 50–51, proof of Theorem 4.4, the sets 𝒬(υ, t) and Υ and display (29)

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.FiberDual

theorem lp_duality {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ ε : ℝ)
    (hε : 0 < ε) (lam s : Fin N → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hfeas : ∃ (υ : Fin N → ℝ) (t : ℝ) (θ : Fin N → ℝ),
      ((∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, υ i ≤ t) ∧ ∑ i, υ i = 1 ∧
        (N : ℝ)⁻¹ ≤ t ∧ t ≤ ((N : ℝ) * ε)⁻¹) ∧
      ((∀ i, 0 ≤ θ i) ∧
        ∑ i ∈ I, (θ i + (t - υ i) * d i) + ∑ i ∈ Iᶜ, (θ i + υ i * d i) ≤ N * ρ * t)) :
    (⨆ (υ : Fin N → ℝ) (t : ℝ) (θ : Fin N → ℝ)
        (_ : ((∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, υ i ≤ t) ∧ ∑ i, υ i = 1 ∧
            (N : ℝ)⁻¹ ≤ t ∧ t ≤ ((N : ℝ) * ε)⁻¹) ∧
          ((∀ i, 0 ≤ θ i) ∧
            ∑ i ∈ I, (θ i + (t - υ i) * d i) + ∑ i ∈ Iᶜ, (θ i + υ i * d i) ≤ N * ρ * t)),
      ((∑ i, (θ i * lam i + υ i * s i) : ℝ) : EReal)) =
    ⨅ (v : DualPt N) (_ : InV d I ρ v ∧ v.lam = lam ∧ v.s = s),
      ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal) := by sorry

end CondPortOT.FiberDual
