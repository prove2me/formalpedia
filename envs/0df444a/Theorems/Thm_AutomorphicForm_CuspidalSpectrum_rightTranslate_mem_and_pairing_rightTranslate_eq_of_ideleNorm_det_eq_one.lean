-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
-- name    : AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/30a7b7c1-399c-5a0a-800c-b3665e02c76c
-- title:
--   Right translation by determinant-norm-one elements is unitary
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be real numbers and let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, written `AdelicGL2 (𝓞 F) F`, which is assumed to be a slab fundamental domain in the sense of `IsSlabFundamentalDomain`: $0<\alpha<\beta$, every $g\in\Phi_0$ satisfies $\lVert\det g\rVert\in[\alpha,\beta]$ (the idele norm being the value of the distributive Haar character of $\mathbb{A}_F$), and $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` on the slab $\{g:\lVert\det g\rVert\in[\alpha,\beta]\}$, equipped with the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A}_F)$ restricted to that slab. Let $\sigma$ be a real number, let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^{\times}$ to $\mathbb{C}^{\times}$, and let $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ both lie in `contMemberSubmodule F Φ₀ ξ`, that is, each is continuous and satisfies the automorphy predicate `IsAutomorphicFnAt F (fdPins F Φ₀) ξ`. Finally let $y\in\mathrm{GL}_2(\mathbb{A}_F)$ with $\lVert\det y\rVert=1$. Then the translates $x\mapsto\varphi(xy)$ and $x\mapsto\psi(xy^{-1})$ again lie in `contMemberSubmodule F Φ₀ ξ`, and for the weighted pairing $\langle a,b\rangle_\sigma=\int_{\Phi_0}a(x)\overline{b(x)}\,\lVert\det x\rVert^{-\sigma}\,dx$ one has $\langle\varphi(\cdot\,y),\psi\rangle_\sigma=\langle\varphi,\psi(\cdot\,y^{-1})\rangle_\sigma$.
--
--   This is the unitarity (adjointness) of right translation by an adelic matrix of idele-norm-one determinant on the weighted $L^2$-pairing of automorphic functions over a slab fundamental domain, with no restriction on the weight $\sigma$ or on the character $\xi$. It underlies the construction of self-adjoint and unitary translation operators in the cuspidal spectrum, and is used in the treatment of Hecke-type averages over cosets and of orthogonality statements for level-spherical functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ) (hψ : ψ ∈ contMemberSubmodule F Φ₀ ξ)
    (y : AdelicGL2 (𝓞 F) F)
    (hy : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) = 1) :
    rightTranslate F y φ ∈ contMemberSubmodule F Φ₀ ξ ∧
    rightTranslate F y⁻¹ ψ ∈ contMemberSubmodule F Φ₀ ξ ∧
    pairing F Φ₀ σ (rightTranslate F y φ) ψ = pairing F Φ₀ σ φ (rightTranslate F y⁻¹ ψ) := by sorry
