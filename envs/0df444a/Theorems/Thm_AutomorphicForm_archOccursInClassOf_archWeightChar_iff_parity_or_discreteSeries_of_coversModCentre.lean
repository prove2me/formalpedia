-- Prove2me | Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre
-- name    : AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/30abf03e-e089-5e4d-bfb5-5e2508baf273
-- title:
--   Archimedean K-types of a class: parity or discrete series
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$, and write $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\ F\ c\ u\ d_1\ d_2\}$, where `centreCutSiegelSet` consists of those adelic matrices whose finite part lies in `finiteIntegralGL2`, all of whose archimedean components have local height $\ge c$ and $x$-window square $\le u^2$, and whose archimedean determinant norms at every infinite place lie in $[d_1,d_2]$. Assume `CoversModCentre F D`: every $g\in\mathrm{GL}_2(\mathbb A_F)$ can be written so that $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ and some central adelic scalar $z$. Let $\Theta$ be a complex Hecke eigensystem over $F$ (a nonzero level ideal together with families $a,b$ indexed by the height-one primes of $\mathcal O_F$), and assume `ArchOccursInClassOf F D \Theta` holds for the trivially true predicate: some eigensystem $\Theta'$ agreeing with $\Theta$ in both families away from a finite set of primes admits a smooth cusp realization, at the production pins built on $D$, of the central rescaling $\Theta'.\mathrm{toRawCentral}$ whose underlying function is continuous. Fix a real place $w$ of $F$, with $\mathrm{hw}: w$ real. Say that a character $\chi$ of `rowIsometrySubgroup₀ ℝ` *occurs* when `ArchOccursInClassOf F D Θ` holds for the predicate asserting `HasArchCharacterAt₀ F w` for $\chi$ transported to $w$ along the isomorphism $F_w\cong\mathbb R$, i.e. some eigensystem agreeing with $\Theta$ away from finitely many primes has a continuous smooth cusp realization on $D$ transforming by $\chi$ under the rotation subgroup at $w$. The conclusion is threefold: (1) every occurring $\chi$ equals $\mathrm{archWeightChar}_{\mathbb R}(n)$ for some $n\in\mathbb Z$; (2) either there is $\varepsilon\in\mathbb Z$ with $\mathrm{archWeightChar}_{\mathbb R}(n)$ occurring exactly when $n-\varepsilon$ is even, or there is $k\ge 2$ with $\mathrm{archWeightChar}_{\mathbb R}(n)$ occurring exactly when $k\le|n|$ and $n-k$ is even; and (3) for every $k\ge 2$, the conjunction of the weight-$k$ transformation law with `IsArchLowestWeightAt w hw` (existence of $\sigma\in\mathbb C$ making $z\mapsto (\operatorname{Im} z)^{\sigma}\varphi(g\,\iota_w(\text{Iwasawa section}(z)))$ holomorphic for all $g$) occurs in the class of $\Theta$ on $D$ if and only if the set of occurring weights is exactly $\{n : k\le|n|,\ n\equiv k \bmod 2\}$.
--
--   This records that the archimedean profile at a real place of a cuspidal near-equivalence class is the $\mathrm{SO}(2)$-type profile of a single infinite-dimensional irreducible unitary representation of $\mathrm{GL}_2(\mathbb R)$: a full parity class (principal or complementary series) or a discrete-series tail, the latter being detected by a lowest-weight vector in the sense of holomorphy. It feeds the Langlands–Tunnell part of the argument, where it is used in the comparison of a formal base change with its twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLowestWeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    (∀ χ : rowIsometrySubgroup₀ ℝ →* ℂˣ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w
            (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
              (norm_ringEquivRealOfIsReal hw))) φ) →
        ∃ n : ℤ, χ = archWeightCharℝ n) ∧
    ((∃ ε : ℤ, ∀ n : ℤ,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w
              ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ) ↔
          Even (n - ε)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n : ℤ,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w
              ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ) ↔
          (k ≤ |n| ∧ Even (n - k)))) ∧
    (∀ k : ℤ, 2 ≤ k →
      (ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w
              ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchLowestWeightAt w hw φ) ↔
        ∀ n : ℤ,
          ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
              (fun φ => HasArchCharacterAt₀ F w
                ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                  (norm_ringEquivRealOfIsReal hw))) φ) ↔
            (k ≤ |n| ∧ Even (n - k)))) := by sorry
