-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_forall_injective_fderiv_add_smul
-- name    : FiniteEnergyPlane.exists_forall_injective_fderiv_add_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-08T22:43:20.716531+00:00
-- url     : https://prove2.me/theorems/6547691f-7f2e-4efa-bf82-125ddfd8c568
-- title:
--   Persistence of an injective linearization along a C^1 family
-- statement:
--   Let $E$ be a real normed space, $r>0$, and $g:\mathbb C\times\mathbb R\to E$ of class $C^1$ on $\mathbb C\times(-r,r)$. Fix $z_0\in\mathbb C$ and suppose that the linear map $\mathbb C\times\mathbb R\times\mathbb R\to E$, $(\Delta,\delta t,\lambda)\mapsto Dg(z_0,0)(\Delta,\delta t)+\lambda\,g(z_0,0)$, is injective. Then there is $r'\in(0,r]$ such that for every $t\in(-r',r')$ the linear map $(\Delta,\delta t,\lambda)\mapsto Dg(z_0,t)(\Delta,\delta t)+\lambda\,g(z_0,t)$ is injective.
--
--   The statement says that transversality of a family at one point to the radial direction persists for nearby parameters.
-- source:
--   Standard (openness of injective linear maps on a finite-dimensional space)

import Mathlib

namespace FiniteEnergyPlane

open Topology

/-- Let `g : ℂ × ℝ → E` be `C¹` on `ℂ × (-r, r)` and fix `z₀ : ℂ`. If the linear map
`(Δ, δt, λ) ↦ Dg(z₀, 0)(Δ, δt) + λ • g(z₀, 0)` is injective, then for some `r' ∈ (0, r]` the
linear map `(Δ, δt, λ) ↦ Dg(z₀, t)(Δ, δt) + λ • g(z₀, t)` is injective for every `t ∈ (-r', r')`. -/
theorem exists_forall_injective_fderiv_add_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) (g : ℂ × ℝ → E)
    (hg : ContDiffOn ℝ 1 g (Set.univ ×ˢ Set.Ioo (-r) r)) (z₀ : ℂ)
    (h0 : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (z₀, 0) (Δ, δt) + lam • g (z₀, 0) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0) :
    ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ (Δ : ℂ) (δt lam : ℝ),
      fderiv ℝ g (z₀, t) (Δ, δt) + lam • g (z₀, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  sorry

end FiniteEnergyPlane
