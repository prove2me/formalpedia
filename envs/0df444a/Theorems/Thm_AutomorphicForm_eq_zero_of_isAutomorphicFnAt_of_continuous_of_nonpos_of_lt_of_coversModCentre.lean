-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
-- name    : AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/913d9023-2d41-560f-8e2b-741bd14863eb
-- title:
--   Covering centre-cut Siegel window with c ≤ 0 forces vanishing
-- statement:
--   Let $F$ be a number field, let $c, u, d_1, d_2$ be real numbers and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F$ is the adele ring of $F$. Write $\mathfrak{S} =$ `centreCutSiegelSet F c u d₁ d₂` for the set of $g \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite part `glFin` lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and with `archDetNorm` $w\, g \in [d_1,d_2]$ for every $w$; and let $D = \bigcup_{x \in T} \mathfrak{S}x$ be the union of the right translates. Assume $c \le 0$, $d_1 < d_2$, and `CoversModCentre F D`: for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ there exist $\gamma \in \mathrm{GL}_2(F)$ and $z \in \mathbb{A}_F^\times$ with $\mathrm{globalPoints}(\gamma)\, g\, \mathrm{centralScalar}(z) \in D$. Let `pins` be `productionPinsOf F D` with the level subgroups $N \mapsto$ `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F` (the preimage under `glFin` of the level-one congruence subgroup intersected with the kernel of `glArch`), the Hecke generators $v \mapsto$ `heckeGen (𝓞 F) F v`, and the box `adelicBox F`; thus the measurable structure is `glBorel`, the measure is the Haar measure `adelicGLHaar`, the region is $D$, the central subgroup is $\top \le \mathbb{A}_F^\times$, and the additive datum is Haar measure on $\mathbb{A}_F$ conditioned on `adelicBox F`. Let $\xi : \top \to \mathbb{C}^\times$ be a character and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy `IsAutomorphicFnAt F pins ξ φ`, i.e. the predicate `LsXiMember` for the measure, central subgroup, character $\xi$ and region recorded in `pins`. If $\varphi$ is continuous, then $\varphi = 0$.
--
--   This is the degenerate case of the reduction-theory input: a centre-cut Siegel window whose height floor $c$ is non-positive is too large for any non-zero continuous $\xi$-equivariant automorphic function to satisfy the integrability condition on it, even when the window covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo rational points and the centre. It is invoked by the statements about cuspidal constituents and isotypic cusp submodules over such windows, which are thereby reduced to windows with positive height floor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean

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

theorem AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : c ≤ 0) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ) :
    φ = 0 := by sorry
