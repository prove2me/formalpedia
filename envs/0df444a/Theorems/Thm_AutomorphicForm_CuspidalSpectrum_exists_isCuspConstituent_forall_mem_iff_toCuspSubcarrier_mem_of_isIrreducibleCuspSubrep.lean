-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/d9a01b3c-b6d4-5412-b6a0-2daeed4abc04
-- title:
--   Cuspidal constituent attached to an irreducible closed cusp subrepresentation
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $W=\bigcup_{x\in T}\,\{g x : g\in\mathfrak S\}$, where $\mathfrak S=\mathtt{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$ consists of the $g$ whose finite component lies in the integral subgroup, whose local height at every infinite place is at least $c$, whose $x$-window square at every infinite place is at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; assume $W$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo $\mathrm{GL}_2(F)$ on the left and the adelic central torus on the right. Let $\xi$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$ with $\|\xi(z)\|=\|z\|^{\sigma}$ for all $z$, where $\|\cdot\|$ is the idele norm. Let $\Phi_0$ be a slab fundamental domain for parameters $0<\alpha<\beta$, i.e. $\Phi_0$ lies in the slab $\{\,\|\det g\|\in[\alpha,\beta]\,\}$ and is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the adelic Haar measure restricted to that slab. Let $M$ be a $\mathbb{C}$-submodule of the cuspidal subcarrier $\mathtt{cuspSubcarrier}\,F\,h_{\Phi_0}\,\sigma\,\xi$ (the closure in $L^2$ of the weighted measure of the classes of continuous cuspidal automorphic members) which is an irreducible closed cusp subrepresentation: $M$ is closed, nonzero, stable under every continuous operator lifting a finite-adelic right translation, a right translation by a row-isometry element at an infinite place, or a right convolution by a factorisable archimedean-bi-finite test function, and every closed cusp subrepresentation contained in $M$ is $0$ or $M$. Then there is a $\mathbb{C}$-submodule $V$ of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cuspidal constituent for the character $\xi$ at the production pins of $W$ (Haar measure and Borel structure on $\mathrm{GL}_2(\mathbb{A}_F)$, carrier $W$, full central subgroup, level subgroups $\mathtt{levelOne}\,N\sqcap\mathtt{finiteAdelicGL2Subgroup}$, Hecke generators $\mathtt{heckeGen}$, and additive Haar measure conditioned on the adelic box), that is, $V$ is a cusp subrepresentation inside the $K$-finite cuspidal submodule at these pins, $V\neq 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$; and $V$ is characterised by: a function $\psi$ lies in $V$ if and only if $\psi$ lies in the $K$-finite cuspidal submodule at these pins and $\psi$ is a continuous cuspidal automorphic member at $\Phi_0$ whose class $\mathtt{toCuspSubcarrier}\,F\,h_{\Phi_0}\,\sigma\,\xi\,\psi$ in the cuspidal subcarrier belongs to $M$.
--
--   This is the passage from the $L^2$ picture to the algebraic one: an irreducible closed invariant subspace of the cuspidal subcarrier is cut out, on the level of $K$-finite smooth cusp functions, by a cuspidal constituent, so that abstract irreducible cuspidal representations correspond to irreducible spaces of automorphic functions. It is used in the decomposition of isotypic cuspidal spaces as a supremum of cuspidal constituents and in the construction of orthonormal bases of level-one isotypic cusp spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_isCuspConstituent_forall_mem_iff_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) :
    ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V ∧
      ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, ψ ∈ V ↔
        ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧
          ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M := by sorry
