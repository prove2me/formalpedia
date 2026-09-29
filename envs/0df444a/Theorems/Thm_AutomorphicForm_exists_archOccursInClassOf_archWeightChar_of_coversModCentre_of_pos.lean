-- Prove2me | Theorems.Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
-- name    : AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/2b93fbbc-342b-52f9-9e68-037b5ba07f3a
-- title:
--   Occurrence of a weight character at a real place
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$ for the union of the right translates by the elements of $T$ of the centre-cut Siegel set $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂`, consisting of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has local height at least $c$ and window coordinate with $\mathrm{xWindowSq}\le u^{2}$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every infinite place $w$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and a unit idele $z$ with $\gamma g\,z\in D$. Let $\Theta$ be a Hecke eigensystem over $F$ with complex coefficients (a nonzero level ideal together with families $a_v,b_v$ over the height-one primes), and assume `ArchOccursInClassOf F D Θ` holds for the trivial predicate, i.e. some eigensystem $\Theta'$ whose $a$- and $b$-families agree with those of $\Theta$ outside a finite set of primes carries a smooth cusp realization at the production pins attached to $D$ (level subgroups `levelOne ⊓ finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, conditioning set `adelicBox`, full central subgroup) for $\Theta'$`.toRawCentral` (same level and $a$, with $b_v$ scaled by $(\mathrm{cNorm}\,v)^{-1}$) whose underlying function is continuous. Let $w$ be a real infinite place of $F$. Then there is an integer $n$ such that the same occurrence statement holds for $\Theta$ on $D$ with the predicate cutting out those functions $\varphi$ satisfying `HasArchCharacterAt₀ F w χ_n`, where $\chi_n$ is the weight-$n$ character `archWeightCharℝ n` transported along the norm-preserving identification `ringEquivRealOfIsReal hw` of the completion at $w$ with $\mathbb{R}$ by `rowIsometrySubgroup₀Map`.
--
--   This is the existence of a vector of pure type under the maximal compact (rotation) subgroup at a real place inside a cuspidal near-equivalence class, formulated for continuous realizations on a fixed covering Siegel window. It feeds the corresponding statement without the positivity hypotheses on $c$ and $d_1$, and the analysis of archimedean Casimir eigenvalues and Whittaker coefficients used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ n : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ) := by sorry
