-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot
-- name    : AutomorphicForm.isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/49e3522b-5f22-5bb3-8292-a371ae73c529
-- title:
--   Isotypic cusp spaces shrink when the determinant floor is lowered
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,d_1'$ be reals and let $T$ be a finite subset of $GL_2(\mathbb{A}_F)$. Assume $c>0$, $d_1\le d_1'$, $0<d_1'$ and $d_1'<d_2$, and that the set $D_{d_1}=\bigcup_{x\in T}(\,\cdot\,x)\big(\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\big)$ — the right translates by $T$ of the set of $g$ whose finite part is integral, whose archimedean components satisfy $\mathrm{localHeight}\ge c$ and $\mathrm{xWindowSq}\le u^2$ at every infinite place, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every infinite place $w$ — covers $GL_2(\mathbb{A}_F)$ modulo $GL_2(F)$ on the left and the adelic centre on the right. Let $D_{d_1'}$ be the analogous union with floor $d_1'$. Both windows are packaged by `productionPinsOf` with the Borel structure and Haar measure on $GL_2(\mathbb{A}_F)$, central subgroup $Z=\top$, level subgroups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}(v)$, and the additive Haar measure conditioned on $\mathrm{adelicBox}\,F$. Fix a character $\xi$ of $Z$, an ideal $N$, a finite set $S$ of finite places and a Hecke eigensystem $\Psi$ over $\mathbb{C}$. If the $\mathbb{C}$-span of the isotypic cusp forms for $(\xi,N,S,\Psi)$ read at the window $D_{d_1}$ is non-zero, then the corresponding span at $D_{d_1'}$ is contained in it.
--
--   Only the square-integrability clause of the isotypic cusp condition depends on the window, so this is the transport statement that carries results proved at windows of positive determinant floor (hence finite volume) back to a window whose floor may reach $0$. It is used in the decomposition of elements of an isotypic cusp space under right convolution and an archimedean cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (hne : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≠ ⊥) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤
      isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ := by sorry
