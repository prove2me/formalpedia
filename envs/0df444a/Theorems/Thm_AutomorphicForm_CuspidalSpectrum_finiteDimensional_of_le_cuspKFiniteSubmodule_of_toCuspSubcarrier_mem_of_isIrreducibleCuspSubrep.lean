-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
-- name    : AutomorphicForm.CuspidalSpectrum.finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/9511c49b-7892-5c66-9840-5d6c7807c4db
-- title:
--   Admissibility of irreducible closed cuspidal subrepresentations, at function level
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$ such that the set $W=\bigcup_{x\in T}\,\{g x : g\in \mathfrak S\}$, with $\mathfrak S$ the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (finite part integral, all local heights $\ge c$, all window squares $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$), covers $\mathrm{GL}_2(\mathbb A_F)$ modulo global points and central scalars. Let $\xi$ be a character of the full idele unit group with $\lVert\xi(z)\rVert$ equal to the $\sigma$-th power of the idele norm of $z$, and let $\Phi_0$ be a slab fundamental domain for the global points in the determinant-norm slab $[\alpha,\beta]$, $0<\alpha<\beta$. Let $M$ be a submodule of the cuspidal subcarrier $\mathrm{cuspSubcarrier}\,F\,h_{\Phi_0}\,\sigma\,\xi$ which is an irreducible closed cusp subrepresentation: closed, stable under the cusp lifts of right translation by finite-adelic elements and by archimedean row isometries and of right convolution by factorizable archimedean-bi-finite test functions, non-zero, and having no proper non-zero closed cusp subrepresentation. Let $U=O\cap\mathrm{GL}_2(\mathbb A_F)_{\mathrm f}$ be compact with $O$ an open subgroup and $\mathrm{GL}_2(\mathbb A_F)_{\mathrm f}$ the kernel of the archimedean projection, and let $\mathrm{tys}$ be a family of archimedean types. Then every $\mathbb C$-submodule $Y$ of functions $\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ which is contained in the $K$-finite cuspidal submodule for the production pins of $W$ (level subgroups $\mathrm{levelOne}(N)\cap\mathrm{GL}_2(\mathbb A_F)_{\mathrm f}$, Hecke generators $\mathrm{heckeGen}$, adelic box), all of whose members $\psi$ lie in $\mathrm{cuspMemberSubmodule}\,F\,\Phi_0\,\xi$ with class $\mathrm{toCuspSubcarrier}\,\psi\in M$, which satisfies $\psi(gk)=\psi(g)$ for all $g$ and all $k\in U$, and which lies in the archimedean cut submodule of $\mathrm{tys}$, is finite-dimensional over $\mathbb C$.
--
--   This is the admissibility of an irreducible closed subrepresentation of the cuspidal spectrum, read at the grain of functions rather than of abstract representations: for a fixed compact level and a fixed finite family of archimedean types, the $K$-finite cusp forms whose $L^2$-classes lie in $M$ form a finite-dimensional space. It feeds the passage from irreducible closed cuspidal subrepresentations to cuspidal constituents, where an arbitrary $K_f$-smooth vector must be placed inside such a finite-dimensional cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep.lean

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

theorem AutomorphicForm.CuspidalSpectrum.finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYK : Y ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hYM : ∀ ψ ∈ Y, ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥Y := by sorry
