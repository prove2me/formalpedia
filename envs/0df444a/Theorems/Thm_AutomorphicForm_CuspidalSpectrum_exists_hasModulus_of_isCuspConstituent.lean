-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7b5e4cb6-24ae-56f2-93a0-6981598e6740
-- title:
--   Cuspidal constituents force a modulus on ξ
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, let $\xi$ be a homomorphism from the full subgroup $\top$ of the idele group $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of the space of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$. Consider the carrier data `productionPinsOf` whose Borel structure and measure on $\mathrm{GL}_2(\mathbb{A}_F)$ are `glBorel` and the adelic Haar measure, whose central subgroup is all of $\mathbb{A}_F^\times$, whose level subgroups are $N\mapsto$ `levelOne` at $N$ intersected with the kernel of the archimedean projection, whose Hecke elements are the `heckeGen` at each finite place, whose ambient measure on $\mathbb{A}_F$ is the conditional Haar measure on the adelic box, and whose domain is $\bigcup_{x\in T}\{gx : g\in$ `centreCutSiegelSet` $F\,c\,u\,d_1\,d_2\}$, the Siegel set consisting of those $g$ whose finite part is integral and whose archimedean components satisfy $c\le$ `localHeight`, `xWindowSq` $\le u^2$, and `archDetNorm` $\in[d_1,d_2]$ at every infinite place. Assume $V$ is a cuspidal constituent for these data and $\xi$: that is, $V$ is contained in the $K$-finite cuspidal submodule, is stable under right translation by the elements of the finite-adelic subgroup and by the archimedean row-isometry subgroups, is stable under right convolution by factorizable archimedean-bi-finite test functions, is non-zero, and contains no proper non-zero submodule with these stability properties. Then there exists a real $\sigma$ such that $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{\sigma}$ for every idele $z$, where $\|\cdot\|_{\mathbb{A}}$ is the idele norm.
--
--   This is the statement that the central character of a cuspidal constituent of $\mathrm{GL}_2$ over a number field is of bounded type, i.e. has absolute value a real power of the idele norm; the exponent $\sigma$ is what later weights the inner product on the cuspidal spectral carrier. It is invoked by the eigen-capture and finite-dimensionality statements for cuspidal constituents, such as [`AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos`](thm.html#AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ σ : ℝ, HasModulus F ξ σ := by sorry
