-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
-- name    : AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/7d7ac239-b86f-5a5f-8044-6d821e51b46a
-- title:
--   Isotypic cusp forms persist under projection to a closed subrepresentation
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2$ over the adele ring of $F$ such that the window $W=\bigcup_{x\in T}(\,\cdot\,x)[\,\mathrm{centreCutSiegelSet}\ F\ c\ u\ d_1\ d_2\,]$ satisfies `CoversModCentre`, i.e. every adelic matrix $g$ can be written with $\gamma g z\in W$ for some $\gamma\in\mathrm{GL}_2(F)$ and some central idelic scalar $z$. Let $\xi$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$ with $\|\xi(z)\|=\|z\|^{\sigma}$ for all $z$ (modulus $\sigma$, with $\|\cdot\|$ the idele norm), and let $\Phi_0$ be a slab fundamental domain for $\mathrm{GL}_2(F)$ acting on the determinant-norm slab $[\alpha,\beta]$. Fix an ideal $N$ of $\mathcal{O}_F$, a finite set $S$ of finite places, a Hecke eigensystem $\Psi$ over $\mathbb{C}$, and a submodule $M$ of the cuspidal subcarrier $\mathrm{cuspSubcarrier}\ F\ h_{\Phi_0}\ \sigma\ \xi$ inside $L^2$ of the weighted measure, assumed to be a closed cuspidal subrepresentation (closed, and stable under every continuous lift of right translation by finite-adelic elements and by archimedean row isometries, and under lifts of right convolution by factorizable archimedean-bi-finite test functions). Write `pins` for the production pins attached to $W$, with level groups $U(N)=\mathrm{levelOne}(N)\cap\mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $\mathrm{heckeGen}\ v$ and the box $\mathrm{adelicBox}$. Let $\varphi$ be an isotypic cusp form at these pins for the datum $(\xi,N,S,\Psi)$ — smooth cuspidal automorphic with central character $\xi$, continuous, right $U(N)$-invariant, a Hecke coset eigenfunction with eigenvalue $\Psi.a(v)$ for each $v\notin S$, and satisfying the central eigenvalue equation with constant $(\mathrm{cNorm}\ v)^{-1}\Psi.b(v)$ — and assume $\varphi$ lies in the cuspidal member submodule at $\Phi_0$. Let $\psi$ lie in the $K$-finite cuspidal submodule at these pins (the span of continuous functions all of whose right translates are smooth cuspidal automorphic and which lie in some archimedean cut submodule) and in the cuspidal member submodule at $\Phi_0$, with the $L^2$-class of $\psi$ in $M$ and the $L^2$-class of $\varphi-\psi$ in $M^{\perp}$. Then $\psi$ is again an isotypic cusp form at these pins for the same datum $(\xi,N,S,\Psi)$.
--
--   This is the step which says that the orthogonal projection onto a closed cuspidal subrepresentation of the $L^2$-class of an isotypic cusp form is realised by a function that is again isotypic for the same Hecke datum: the projection commutes with the lifts of the level-group translations, of the Hecke coset sums and of the central translations, and the resulting identities of functions are recovered from the identities of $L^2$-classes. It is used in the decomposition of an isotypic cuspidal space into cuspidal constituents, in particular by [`AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul`](thm.html#AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul). Note that the isotypy predicate is satisfied by the zero function, so no non-vanishing assumption on $\psi$ appears.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal.lean

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

theorem AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψK : ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hψM : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ M)
    (hperp : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ Mᗮ) :
    IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ψ := by sorry
