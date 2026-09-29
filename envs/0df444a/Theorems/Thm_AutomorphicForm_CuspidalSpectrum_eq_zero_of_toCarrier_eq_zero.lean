-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
-- name    : AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/f63d2246-38e0-53f7-9d70-c2ba99af4b7a
-- title:
--   Continuous members inject into the weighted L² carrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb{R}$ and let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ (written `AdelicGL2 (𝓞 F) F`) which is a slab fundamental domain in the sense of `IsSlabFundamentalDomain F α β Φ₀`: one has $0<\alpha<\beta$, every $g\in\Phi_0$ satisfies $\lVert\det g\rVert_{\mathbb{A}}\in[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` on the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` restricted to the slab $\{g:\lVert\det g\rVert_{\mathbb{A}}\in[\alpha,\beta]\}$. Let $\sigma\in\mathbb{R}$, let $\xi$ be a homomorphism from the full subgroup of the idele units $(\mathbb{A}_F)^\times$ to $\mathbb{C}^\times$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ lie in `contMemberSubmodule F Φ₀ ξ`, i.e. $\varphi$ is continuous and satisfies the predicate `IsAutomorphicFnAt F (fdPins F Φ₀) ξ φ` defining `memberSubmodule`, which supplies left invariance of $\varphi$ under global points, the central-character relation $\varphi(z\cdot g)=\xi(z)\varphi(g)$ for central scalars, and the integrability needed below. Assume that the image of $\varphi$ under `toCarrier F hΦ₀ σ ξ`, namely its class in $L^2$ of the weighted measure $\lVert\det g\rVert_{\mathbb{A}}^{-\sigma}\,dg$ on $\Phi_0$, is zero. Then $\varphi$ is the zero function on all of $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the injectivity of the passage from continuous automorphic members to their classes in the weighted $L^2$ carrier attached to a slab fundamental domain; it is what converts Hilbert-space statements about the carrier (vanishing of a component, finite-dimensionality of an image) back into pointwise statements about functions. It is used throughout the analysis of cuspidal constituents, for instance in the results producing eigenvectors and convolution decompositions inside isotypic cusp submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ)
    (h0 : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩ = 0) : φ = 0 := by sorry
