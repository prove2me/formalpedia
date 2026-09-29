-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero
-- name    : AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/0eff8375-b80b-59bb-9ba5-51da8627add4
-- title:
--   Narrow-window K-finite cusp space sits in the wide-window one
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,d_1'$ be reals and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $F$, subject to $0<c$, $d_1\le d_1'$, $0<d_1'$ and $d_1'<d_2$. Write $W=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$ and $W'$ for the same union with $d_1$ replaced by $d_1'$, where `centreCutSiegelSet` consists of the $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean components satisfy, at every infinite place $w$, $c\le \mathrm{localHeight}$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Assume `CoversModCentre F W`, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele class $z$ with $\gamma g\,z\in W$ (images under `globalPoints` and `centralScalar`). Let $\xi$ be a character of the group $Z=\top$ of the production pins attached to $W$ (Borel $\sigma$-algebra and adelic Haar measure on $\mathrm{GL}_2$, level groups $N\mapsto \mathrm{levelOne}\sqcap \mathrm{finiteAdelicGL2Subgroup}$, Hecke generators `heckeGen`, and the adelic additive Haar measure conditioned on `adelicBox`), and assume there is a continuous non-zero $\varphi$ with `IsAutomorphicFnAt` for those pins and $\xi$, i.e. $\varphi$ lies in the $L^2$-$\xi$ space over $W$. Then `cuspKFiniteSubmodule` for the pins of $W'$ and $\xi$ is contained in `cuspKFiniteSubmodule` for the pins of $W$ and $\xi$; that is, the $\mathbb{C}$-span of the continuous functions all of whose right translates are smooth cusp automorphic at the narrow pins and which lie in some `archCutSubmodule` is contained in the corresponding span for the wide window.
--
--   Since only the determinant window entering the square-integrability clause differs between the two sets of pins, this is the non-trivial half of the statement that the $K$-finite smooth cuspidal space attached to a covering centre-cut Siegel window does not depend on the determinant floor. It feeds the identification of cuspidal constituents at different pins, being used in the two results that place a member of an isotypic cusp submodule, cut by archimedean types, in the supremum of cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (hne : ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ ∧ Continuous φ ∧ φ ≠ 0) :
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by sorry
