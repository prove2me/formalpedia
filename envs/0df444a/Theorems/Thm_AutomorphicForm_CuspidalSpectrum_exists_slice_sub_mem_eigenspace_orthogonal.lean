-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal
-- name    : AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/44b41e1d-f198-5d73-b475-f4b9536a16b5
-- title:
--   Spectral μ-components of isotypic cusp forms are eigenfunction classes
-- statement:
--   Let $F$ be a number field and let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$ such that the set $D=\bigcup_{x\in T}(\cdot\,x)[\,\Sigma\,]$ of right translates of the centre-cut Siegel set $\Sigma=$ `centreCutSiegelSet F c u d₁ d₂` (finite part in $\mathrm{GL}_2$ of the integral finite adeles, local height $\ge c$, window $x$-coordinate squared $\le u^2$, archimedean determinant norm in $[d_1,d_2]$ at every infinite place) covers modulo the centre: every $g$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ and some central adelic scalar $z$. Let $\xi$ be a homomorphism from the full group of ideles to $\mathbb{C}^\times$, $N\neq 0$ an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, `tys` an archimedean type family, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$. Write `pins` for the production pins with domain $D$, central subgroup everything, level groups $U(N)=$ `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, Hecke generators `heckeGen`, and box `adelicBox F`. Let $x:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ lie in the intersection of `isotypicCuspSubmodule` for these data — the span of the continuous smooth cuspidal automorphic functions with central character $\xi$ that are right $U(N)$-invariant, are Hecke eigenfunctions with eigenvalue $\Psi.a\,v$ for $v\notin S$ and satisfy the central-translate relation with $\Psi.b\,v$ — with `archCutSubmodule F tys`, the intersection over infinite places $w$ of the sum of the type submodules of the representations `tys.rep w i`. Let $\Phi_0$ be a slab fundamental domain of parameters $\alpha,\beta$, let $\sigma$ be such that $\|\xi(z)\|=\|z\|^{\sigma}$ for all ideles $z$, and assume $x$ lies in `cuspMemberSubmodule F Φ₀ ξ`, the continuous smooth cuspidal automorphic functions with central character $\xi$ for the pins attached to $\Phi_0$. Let $f$ be a factorizable test function which is level-spherical of type `tys` for $U(N)$ (so its finite factor is the indicator of the image of $U(N)$) and satisfies $\overline{f(y^{-1})}\,\|\det y\|^{-\sigma}=f(y)$. Let $T_c$ be a continuous linear endomorphism of the cuspidal subcarrier $\mathcal{H}=$ `cuspSubcarrier F hΦ₀ σ ξ` inside $L^2(\Phi_0,\|\det\|^{-\sigma})$ which implements right convolution by $f$ on classes of cuspidal members, and let $\mu\neq 0$. Then there is $\psi$ belonging to `cuspMemberSubmodule F Φ₀ ξ` and to the same intersection `isotypicCuspSubmodule` $\cap$ `archCutSubmodule F tys`, with $\psi * f=\mu\psi$, such that the class of $x-\psi$ in $\mathcal{H}$ is orthogonal to the whole $\mu$-eigenspace of $T_c$.
--
--   This is the spectral-splitting step for isotypic spaces of cusp forms: the $\mu$-spectral part of the $L^2$-class of an isotypic cuspidal vector is realised by a genuine cuspidal member lying in the same Hecke- and archimedean-type cut and satisfying the convolution eigenequation. It is used by [`AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule`](thm.html#AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule) and [`AutomorphicForm.CuspidalConstituent.exists_ne_zero_rightConv_eq_smul_of_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot`](thm.html#AutomorphicForm.CuspidalConstituent.exists_ne_zero_rightConv_eq_smul_of_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot) towards the finite-dimensionality and eigen-decomposition of isotypic cuspidal spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_slice_sub_mem_eigenspace_orthogonal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (x : AdelicGL2 (𝓞 F) F → ℂ)
    (hxi : x ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (hσ : HasModulus F ξ σ) (hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (hflat : flat F σ f = f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
      ψ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ∧
      rightConv F ψ f = μ • ψ ∧
      ∀ y ∈ Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ,
        ⟪toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, y⟫_ℂ = 0 := by sorry
