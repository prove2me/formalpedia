-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightConv_isCompactOperator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/8857142d-d334-5103-a990-5f130994b6b3
-- title:
--   Compact lift of right convolution to the cuspidal sub-carrier
-- statement:
--   Let $F$ be a number field, with $\mathbb{A}_F$ its adele ring and $\mathrm{GL}_2(\mathbb{A}_F)$ carrying the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Let $\alpha,\beta\in\mathbb{R}$ and $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfy `IsSlabFundamentalDomain`, i.e. $0<\alpha<\beta$, $\Phi_0$ lies in the slab where the idele norm of the determinant belongs to $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(F)$ on that slab with the restricted Haar measure. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full unit group of $\mathbb{A}_F$ to $\mathbb{C}^\times$ of modulus $\sigma$, meaning $\|\xi(z)\|$ equals the $\sigma$-th power of the idele norm of $z$ for all $z$. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be factorizable, i.e. $f(g)=f_\infty(g_\infty)\,f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean factor satisfying `IsArchTestFactor` and a finite factor satisfying `IsFinTestFactor`. Then there exists a continuous $\mathbb{C}$-linear operator $T_c$ on the cuspidal sub-carrier $\mathrm{cuspSubcarrier}$ — the topological closure, inside $L^2$ of the weighted measure attached to $(\Phi_0,\sigma)$, of the image of the continuous cuspidal $\xi$-automorphic members — such that $T_c$ is a `IsCuspLift` of $\varphi\mapsto \mathrm{rightConv}\,\varphi\, f$, that is $T_c$ applied to the class of any such member $\varphi$ equals the class of $g\mapsto\int \varphi(gx)f(x)\,dx$ whenever the latter is again such a member, and $T_c$ is a compact operator.
--
--   This is the adelic form of Godement's compactness assertion for smoothing (right convolution) operators on the space of $L^2$ cusp forms on $\mathrm{GL}_2$ over a number field, packaged so that the operator lives on the cuspidal sub-carrier attached to a slab fundamental domain. It supplies the compact operator used in the passage from an eigen-condition $\varphi * f = \lambda\varphi$ to membership in the sum of irreducible closed cuspidal constituents, and is cited by the two such membership results for the isotypic cuspidal submodule cut by an archimedean condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightConv_isCompactOperator
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc ∧ IsCompactOperator Tc := by sorry
