-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_principal_of_mem_of_sub_mem_orthogonal
-- name    : AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_principal_of_mem_of_sub_mem_orthogonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b8fdd10d-0785-5d03-9026-9b42d65471b0
-- title:
--   Orthogonal component of an isotypic cusp form at principal level
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ such that the set $D=\bigcup_{x\in T}(\,\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,]$ — the union of the right translates by $x\in T$ of the set of $g$ whose finite part is integral, whose local heights at all infinite places are $\ge c$, whose window quantities $\mathrm{xWindowSq}$ are $\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$ — covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo left multiplication by global points and right multiplication by central scalars. Let $\xi$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$ with $|\xi(z)|=\|z\|^\sigma$ for all $z$, let $\Phi_0$ be a slab fundamental domain for the global points in the determinant-norm slab $[\alpha,\beta]$, let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$. Work with the production pins on $D$ whose level family is $N\mapsto \mathrm{principalLevel}(N)\cap \mathrm{finiteAdelicGL2Subgroup}$, whose Hecke generators are the $\mathrm{heckeGen}$ at each finite place, and whose adelic box is $\mathrm{adelicBox}$. Let $M$ be a $\mathbb{C}$-submodule of the cuspidal subcarrier $\mathrm{cuspSubcarrier}\,(h_{\Phi_0},\sigma,\xi)$ which is closed and stable under all continuous lifts of right translation by finite-adelic elements, of right translation by archimedean row isometries, and of right convolution by factorizable archimedean-bifinite test functions. Let $\varphi$ be an isotypic cusp form at those pins with datum $(\xi,N,S,\Psi)$, that is: $\varphi$ is smooth cuspidal automorphic with central character $\xi$, continuous, right invariant under $\mathrm{principalLevel}(N)\cap \mathrm{finiteAdelicGL2Subgroup}$, an eigenfunction of the Hecke coset sums at each $v\notin S$ with eigenvalue $\Psi.a\,v$, and satisfies $\varphi(\mathrm{centralScalar}(\det \mathrm{heckeGen}_v)\,g)=(\mathrm{cNorm}\,v)^{-1}\Psi.b\,v\cdot\varphi(g)$ for $v\notin S$. Assume $\varphi$ lies in $\mathrm{cuspMemberSubmodule}\,(\Phi_0,\xi)$ (smooth cuspidal automorphic and continuous at the level-one pins of $\Phi_0$), and that $\psi$ lies both in the $K$-finite cuspidal submodule at the above pins and in $\mathrm{cuspMemberSubmodule}\,(\Phi_0,\xi)$, with the class of $\psi$ in the cuspidal subcarrier belonging to $M$ and the difference of the classes of $\varphi$ and $\psi$ belonging to $M^{\perp}$. Then $\psi$ is itself an isotypic cusp form at the same pins with the same datum $(\xi,N,S,\Psi)$.
--
--   This is the principal-congruence-level form of the statement that the orthogonal projection onto a closed cuspidal sub-representation of a Hecke-isotypic cusp form again satisfies all the defining conditions of the isotypic datum (level invariance, the Hecke coset eigenvalue equations at the places outside $S$, and the central eigenvalue relations); no non-vanishing of $\psi$ is asserted. It feeds the principal-level constituent dictionary [`AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul`](thm.html#AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_rightConv_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_principal_of_mem_of_sub_mem_orthogonal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_principal_of_mem_of_sub_mem_orthogonal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψK : ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hψM : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ M)
    (hperp : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ Mᗮ) :
    IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ψ := by sorry
