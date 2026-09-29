-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
-- name    : AutomorphicForm.CuspidalSpectrum.exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/fc45637b-5737-5a98-800a-5da852526b98
-- title:
--   Strongly continuous isometric U-action on the cuspidal carrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb R$ and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb A_F)$ satisfy `IsSlabFundamentalDomain F α β Φ₀`, i.e. $0<\alpha<\beta$, every $g\in\Phi_0$ has idele norm of $\det g$ in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ in $\mathrm{GL}_2(\mathbb A_F)$ acting on the Haar measure `adelicGLHaar` restricted to that determinant slab. Let $\sigma\in\mathbb R$ and let $\xi$ be a homomorphism from the full unit group of $\mathbb A_F$ to $\mathbb C^\times$ with `HasModulus F ξ σ`, i.e. $\|\xi(z)\| = \|z\|^{\sigma}$ for the idele norm. Let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb A_F)$ whose underlying set is compact. Then there is a monoid homomorphism $\pi$ from $U$ into the continuous $\mathbb C$-linear endomorphisms of the cuspidal subcarrier $\mathrm{cuspSubcarrier}\,F\,h_{\Phi_0}\,\sigma\,\xi$ (the closure, inside $L^2$ of the weighted measure attached to $\Phi_0$ and $\sigma$, of the image of the continuous cuspidal automorphic members) such that: for each $u\in U$, $\pi(u)$ is a cusp-lift of the right translation $\varphi\mapsto\varphi(\,\cdot\,u)$, meaning that whenever $\varphi$ lies in `cuspMemberSubmodule` and so does its translate, $\pi(u)$ carries the class of $\varphi$ to the class of the translate; each $\pi(u)$ is isometric, $\|\pi(u)v\|=\|v\|$; and for each vector $v$ the orbit map $u\mapsto\pi(u)v$ is continuous on $U$.
--
--   This packages the right-translation action of a compact level subgroup $U$ of $\mathrm{GL}_2(\mathbb A_F)$ as a strongly continuous isometric representation on the cuspidal $L^2$-carrier, the basic unitarity statement underlying the theory of cuspidal automorphic representations. It is used to construct the averaging idempotent over $U$ in [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact), which projects onto the $U$-invariant vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F))) :
    ∃ π : U →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ u : U, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (π u)) ∧
      (∀ (u : U) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π u v‖ = ‖v‖) ∧
      (∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun u : U => π u v) := by sorry
