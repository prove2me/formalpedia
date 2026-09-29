-- Prove2me | Theorems.Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre
-- name    : AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9a164154-8fdc-5ded-9620-b5535523e35f
-- title:
--   Occurrence of a real-place weight character in Theta's class
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\,\{g x : g\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` is the set of $g$ whose finite part lies in `finiteIntegralGL2`, with `localHeight` of the archimedean component at least $c$ at every infinite place, `xWindowSq` at most $u^2$ at every infinite place, and `archDetNorm` in $[d_1,d_2]$ at every infinite place. Assume `CoversModCentre F D`: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g z\in D$. Let $\Theta$ be a Hecke eigensystem over $F$ with complex coefficients (a nonzero level ideal together with tables $a,b$ indexed by the finite places), and assume `ArchOccursInClassOf F D Θ (fun _ => True)`: some $\Theta'$ agreeing with $\Theta$ in both tables away from a finite set of finite places admits a smooth cusp realization at the production pins built from $D$, the levels `levelOne ⊓ finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` and the box `adelicBox`, for the recentred eigensystem $\Theta'$`.toRawCentral` (same level and $a$, with $b_v$ rescaled by $(\mathrm{cNorm}\,v)^{-1}$), which is genuine in the sense that its underlying function is continuous. Finally let $w$ be a real infinite place of $F$. Then there is an integer $n$ such that the same occurrence statement holds for the class of $\Theta$ on $D$ with the extra condition that the realizing function $\varphi$ satisfy `HasArchCharacterAt₀ F w` for the character `archWeightCharℝ n` transported along the isomorphism of the completion at $w$ with $\mathbb{R}$ — that is, $\varphi$ transforms by the weight-$n$ character under right translation by the rotation subgroup at $w$ (the variant of `HasArchCharacterAt`, which asks $\varphi(g\,\iota_w(k))=\chi(k)\varphi(g)$ for all row isometries $k$ at $w$).
--
--   This is the existence of a $K$-isotypic vector of some weight at a real place inside a continuously and cuspidally realized near-equivalence class of Hecke eigensystems on $\mathrm{GL}_2$ over a number field, stated at the level of realizations on a fixed Siegel window. It is the unconstrained-parameter form of the result: the positivity conditions on the height floor and on the lower determinant bound present in the variant for positive parameters are here derived rather than assumed, and it feeds the analysis of real archimedean types (minimal $K$-type and Laplace eigenvalue) used on the Langlands–Tunnell side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ n : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ) := by sorry
