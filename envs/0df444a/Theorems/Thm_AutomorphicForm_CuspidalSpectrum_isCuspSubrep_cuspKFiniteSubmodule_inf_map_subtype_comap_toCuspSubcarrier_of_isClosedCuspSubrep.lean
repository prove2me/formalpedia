-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
-- name    : AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/310aed4d-ba75-5002-9ff2-e90f85e95f24
-- title:
--   K-finite cuspidal preimage of a closed cuspidal sub-representation
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $W=\bigcup_{x\in T}\{g x : g\in\mathrm{centreCutSiegelSet}\}$ for the union of the right translates by the elements of $T$ of the set of $g$ whose finite part is integral, with $c\le \mathrm{localHeight}$ and $\mathrm{xWindowSq}\le u^{2}$ at every infinite place and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every infinite place $w$. Assume `CoversModCentre` for $W$: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g z\in W$. Let $\xi:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be a homomorphism with $\|\xi(z)\|=\|z\|^{\sigma}$ for the idele norm, and let $\Phi_0$ be a slab fundamental domain for $\mathrm{GL}_2(F)$ in the determinant-norm slab $[\alpha,\beta]$, $0<\alpha<\beta$. Let $M$ be a $\mathbb{C}$-submodule of the cuspidal subcarrier $\mathrm{cuspSubcarrier}\,F\,h\Phi_0\,\sigma\,\xi\subseteq L^2(\Phi_0)$ which is closed and satisfies `IsClosedCuspSubrep`, i.e. is carried into itself by every bounded operator lifting a finite-adelic right translation, a right translation by an element of $\mathrm{rowIsometrySubgroup}_0$ at an infinite place, or a right convolution by an archimedean-bi-finite factorizable test function. Let $P_W$ be the production pins over $W$ with central subgroup $\top$, level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $\mathrm{heckeGen}$ and the adelic box. Then the intersection of $\mathrm{cuspKFiniteSubmodule}\,F\,P_W\,\xi$ with the image in functions of $\{\varphi\in\mathrm{cuspMemberSubmodule}\,F\,\Phi_0\,\xi : \mathrm{toCuspSubcarrier}(\varphi)\in M\}$ satisfies `IsCuspSubrep` at $P_W$ for $\xi$: it lies in $\mathrm{cuspKFiniteSubmodule}\,F\,P_W\,\xi$ and is stable under right translation by finite-adelic elements, under right translation by $\mathrm{rowIsometryInclAt}_0$ of row isometries at the infinite places, and under right convolution by factorizable archimedean-bi-finite test functions.
--
--   This is the step passing from a closed invariant subspace of the $L^2$ cuspidal subcarrier back to the smooth $K$-finite cuspidal functions representing it, so that the abstract sub-representation $M$ is matched by a sub-representation of the space of $K$-finite smooth cusp forms at a covering Siegel window. It is used in the extraction of cuspidal constituents and in the finite-dimensionality statement for irreducible closed cuspidal sub-representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep.lean

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

theorem AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ
      (cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ⊓
        Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M)) := by sorry
