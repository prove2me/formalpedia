-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal_principal
-- name    : AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/206990a3-a17c-55fd-b01f-62dcc8fc6a6d
-- title:
--   Isotypic cuspidal slice vector for a μ-eigenvalue, principal level
-- statement:
--   Let $F$ be a number field and let $D=\bigcup_{x\in T}Dx$ be the union of the right translates, by the elements of a finite set $T\subseteq \mathrm{GL}_2(\mathbb{A}_F)$, of the centre-cut Siegel set with parameters $c,u,d_1,d_2$ (finite part integral, local height $\ge c$ at every infinite place, $x$-window square $\le u^2$, archimedean determinant norms in $[d_1,d_2]$), with $0<c$, $0<d_1<d_2$, and assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo the centre: every $g$ satisfies $\gamma g z\in D$ for some $\gamma\in \mathrm{GL}_2(F)$ and some central idele scalar $z$. Fix a homomorphism $\xi$ from the full group of idele units to $\mathbb{C}^\times$, a nonzero ideal $N$ of $\mathcal{O}_F$, a finite set $S$ of finite places, an archimedean type family $\mathrm{tys}$, a Hecke eigensystem $\Psi$ over $\mathbb{C}$, and let the carrier pins be `productionPinsOf` with window $D$, full central subgroup, level family $N\mapsto K(N)\cap\ker(\text{glArch})$ (the principal level met with the finite-adelic subgroup), Hecke generators `heckeGen`, and box `adelicBox`. Let $x:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ lie in the intersection of the isotypic cusp submodule for these pins, $\xi$, $N$, $S$, $\Psi$ (the $\mathbb{C}$-span of the smooth continuous cuspidal automorphic functions that are right invariant under the level subgroup at $N$, are Hecke coset eigenfunctions with eigenvalue $\Psi.a(v)$ outside $S$, and satisfy the central relation with $\Psi.b(v)$ outside $S$) with the archimedean cut $\bigsqcap_w\bigvee_i$ of the type submodules of $\mathrm{tys}$. Let $\Phi_0$ be a slab fundamental domain with parameters $0<\alpha<\beta$, let $\sigma$ be such that $\|\xi(z)\|=\|z\|^{\sigma}$ for all idele units, and assume $x$ is a cuspidal continuous member on $\Phi_0$ for $\xi$. Let $f$ be a factorizable test function, level spherical of type $\mathrm{tys}$ for the level subgroup at $N$ (archimedean test factor, bi-finite of type $\mathrm{tys}$, invariant under conjugation by the row-isometry subgroups, times the indicator of the image of that level subgroup), and flat-symmetric: $\mathrm{flat}_\sigma f=f$. Let $T_c$ be a continuous linear endomorphism of the cuspidal subcarrier (the closure in $L^2(\Phi_0,\|\det\|^{-\sigma})$ of the image of the cuspidal continuous members) which implements right convolution by $f$ on classes of cuspidal continuous members, and let $\mu\neq0$. Then there exists $\psi$, a cuspidal continuous member on $\Phi_0$ for $\xi$, lying in the same isotypic cusp submodule intersected with the archimedean cut, with $\psi*f=\mu\psi$ and such that the class of $x$ minus the class of $\psi$ is orthogonal to the whole $\mu$-eigenspace of $T_c$.
--
--   This is the spectral-splitting step in the $L^2$ theory of cusp forms: the $\mu$-spectral component of an isotypic cusp form is represented, up to a vector orthogonal to the $\mu$-eigenspace, by an eigenfunction of right convolution by $f$ lying in the same Hecke isotypic and archimedean-type cut, here at principal congruence level $K(N)$. It feeds the finite eigen-decomposition [`AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule`](thm.html#AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal_principal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (x : AdelicGL2 (𝓞 F) F → ℂ)
    (hxi : x ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (hσ : HasModulus F ξ σ) (hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (hflat : flat F σ f = f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
      ψ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ∧
      rightConv F ψ f = μ • ψ ∧
      ∀ y ∈ Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ,
        ⟪toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, y⟫_ℂ = 0 := by sorry
