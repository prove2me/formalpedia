-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot
-- name    : AutomorphicForm.CuspidalSpectrum.exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/6fcf53c2-640d-59d0-845b-f46c371a262c
-- title:
--   Non-zero closed cuspidal subrepresentations contain K-finite vectors
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$; assume that the union $W=\bigcup_{x\in T}\{g\cdot x: g\in \mathfrak{S}\}$ of right translates of the centre-cut Siegel set $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` (finite part integral, all archimedean local heights $\ge c$, all archimedean $x$-windows bounded by $u^2$, all archimedean determinant norms in $[d_1,d_2]$) covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in W$. Let $\xi$ be a character of the full group of idele units with modulus $\sigma$, that is $\|\xi(z)\|=\|z\|^{\sigma}$ for the idele norm, and let $\Phi_0$ be a slab fundamental domain for parameters $0<\alpha<\beta$: $\Phi_0$ is contained in the slab where the idele norm of the determinant lies in $[\alpha,\beta]$ and is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the adelic Haar measure restricted to that slab. Let $M$ be a $\mathbb{C}$-submodule of the cuspidal subcarrier `cuspSubcarrier F hΦ₀ σ ξ` (the closure in $L^2$ of the weighted measure of the image of the continuous cuspidal members), assume $M$ is a closed cuspidal subrepresentation, i.e. $M$ is closed and stable under every continuous operator on the subcarrier lifting right translation by a finite-adelic element, right translation by an archimedean row-isometry element, or right convolution with a factorizable archimedean bi-finite test function, and assume $M\neq 0$. Then there is a function $\psi$ on adelic $\mathrm{GL}_2$ with $\psi\neq 0$ which lies in the $K$-finite cuspidal submodule $\mathcal{A}^{K\text{-fin}}_{\mathrm{cusp}}$ attached to the production pins of the covering set $W$, the level subgroups $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` and the adelic box, and which moreover belongs to `cuspMemberSubmodule F Φ₀ ξ`, its class in the cuspidal subcarrier lying in $M$.
--
--   This is the non-vanishing input for passing from a closed (not necessarily irreducible) cuspidal subrepresentation of the $L^2$ cuspidal subcarrier to an actual smooth $K$-finite cuspidal automorphic function representing a vector of it. It is used in the construction of cuspidal constituents from irreducible closed cuspidal subrepresentations and in the production of orthonormal families in the isotypic cuspidal submodules at level one and at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_ne_zero_mem_cuspKFiniteSubmodule_toCuspSubcarrier_mem_of_isClosedCuspSubrep_of_ne_bot
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) (hM0 : M ≠ ⊥) :
    ∃ ψ : AdelicGL2 (𝓞 F) F → ℂ, ψ ≠ 0 ∧
      ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧
      ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M := by sorry
