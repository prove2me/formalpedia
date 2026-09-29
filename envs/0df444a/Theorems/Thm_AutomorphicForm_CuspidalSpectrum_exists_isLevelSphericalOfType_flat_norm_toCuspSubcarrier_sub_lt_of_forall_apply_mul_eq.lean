-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/6f2dd148-c331-5e5a-a955-bf16884be7a4
-- title:
--   Flat level-U spherical approximate identity in the cuspidal subcarrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals and $\Phi_0$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ which is a slab fundamental domain in the sense of `IsSlabFundamentalDomain`: $0<\alpha<\beta$, $\Phi_0$ is contained in the determinant-norm slab cut out by $\alpha,\beta$, and $\Phi_0$ is a fundamental domain for the range of the global points inside $\mathrm{GL}_2(\mathbb{A}_F)$ with respect to the adelic $\mathrm{GL}_2$ Haar measure restricted to that slab. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$ of modulus $\sigma$, i.e. $\|\xi(z)\|=\mathrm{ideleNorm}(z)^{\sigma}$ for all $z$. Let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ contained in the kernel of the archimedean projection `glArch`, whose image under the finite projection `glFin` is open, compact and contained in the finite integral subgroup $\mathrm{finiteIntegralGL2}$. Let $\mathrm{tys}$ be an archimedean type family, that is, for each infinite place $w$ a natural number $\mathrm{card}\,w$ together with $\mathrm{card}\,w$ archimedean representation types at $w$. Let $x:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ lie in `cuspMemberSubmodule F Φ₀ ξ` (a continuous function which is a smooth cuspidal automorphic function at the pin data of $\Phi_0$ with central character $\xi$), satisfy $x(gu)=x(g)$ for all $g$ and all $u\in U$, and lie in the archimedean cut submodule of $\mathrm{tys}$, the infimum over infinite places $w$ of the supremum of the type submodules at $w$ attached to the types $\mathrm{tys}.\mathrm{rep}\,w\,i$. Then for every $\varepsilon>0$ there exists $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that: $f$ is a factorizable test function, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$; $f$ is level-$U$-spherical of type $\mathrm{tys}$, i.e. there is an archimedean test factor $f_\infty$ which is bi-finite for $\mathrm{tys}$ and invariant under conjugation by the row-isometry subgroups at all infinite places, with $f(g)=f_\infty(\mathrm{glArch}\,g)$ times the indicator of $\mathrm{glFin}(U)$ evaluated at $\mathrm{glFin}\,g$; $f$ is fixed by the $\sigma$-flat operation, $f(y)=\overline{f(y^{-1})}\,\mathrm{ideleNorm}(\det y)^{-\sigma}$; and the right convolution $g\mapsto\int x(gy)f(y)\,dy$ against adelic $\mathrm{GL}_2$ Haar measure again lies in `cuspMemberSubmodule F Φ₀ ξ` and its class in the cuspidal subcarrier differs from that of $x$ by less than $\varepsilon$ in norm, the classes being taken under the linear map `toCuspSubcarrier F hΦ₀ σ ξ`.
--
--   This is the approximate-identity step for the cuspidal subcarrier: a single flat, level-$U$-spherical test function of prescribed archimedean type whose right convolution moves a given cuspidal member arbitrarily little in the weighted $L^2$-norm, with the finite level allowed to be an arbitrary compact open integral subgroup rather than a congruence subgroup of a specific shape. It is used in the construction of flat archimedean-bi-finite convolution operators on the cuspidal subcarrier and in the approximation of cuspidal classes by finite sums of translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (hUo : IsOpen ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUc : IsCompact ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUi : (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ⊆ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hxU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, x (g * u) = x g) (hxt : x ∈ archCutSubmodule F tys)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys U f ∧
      flat F σ f = f ∧
      ∃ hxf : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ,
        ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hx⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxf⟩‖ < ε := by sorry
