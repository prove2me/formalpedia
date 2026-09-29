-- Prove2me | Theorems.Thm_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos
-- name    : AutomorphicForm.archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2c121f75-60e2-5444-b5a7-0ee0ed59bc6b
-- title:
--   Lowering-annihilated weight-k witness when weight k-2 is absent
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, $0<c$ and $0<d_1$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\,\mathfrak S\cdot x$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has local height at least $c$ and squared window coordinate at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume `CoversModCentre F D`: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and a central ideles scalar $z$ with $\gamma g z\in D$. Let $\Theta$ be a complex Hecke eigensystem over $F$, let $w$ be a real infinite place and $k\in\mathbb{Z}$. Occurrence in the class of $\Theta$ on $D$ for a predicate $P$ means: some eigensystem $\Theta'$ whose tables $a,b$ agree with those of $\Theta$ outside a finite set of finite places admits a smooth cuspidal realisation $R'$ at the production pins built from $D$, the level-one subgroups intersected with the finite adelic group, the Hecke generators and the adelic box, for the central normalisation $\Theta'.\mathrm{toRawCentral}$, which is genuine and whose underlying function satisfies $P$. Assume that the archimedean weight condition `HasArchCharacterAt₀` at $w$ for the weight-$k$ character `archWeightCharℝ k` transported along the identification `ringEquivRealOfIsReal hw` of $F_w$ with $\mathbb{R}$ occurs in the class of $\Theta$ on $D$, while the same condition for weight $k-2$ does not. Then the conjunction of the weight-$k$ condition with `IsArchLoweringAnnihilatedAt w hw` occurs in the class of $\Theta$ on $D$; the latter asserts that for every $g$ and every $z$ in the upper half-plane the slice $m\mapsto\varphi\bigl(g\cdot\iota_w(m)\bigr)$ (defined for $\det m\neq0$ via $F_w\cong\mathbb{R}$, and $0$ otherwise) is differentiable at $\begin{pmatrix}\mathrm{Im}\,z&\mathrm{Re}\,z\\0&1\end{pmatrix}$ and is killed there by the lowering operator $f\mapsto\bigl(Df_m(m\,\mathrm{diag}(1,-1))-i\,Df_m(m\,\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right))\bigr)/2$.
--
--   This is the lowest-weight-vector step in the archimedean theory: if weight $k$ occurs at the real place $w$ but weight $k-2$ does not, then a witness of weight $k$ can be chosen annihilated by the weight-lowering operator, which is the holomorphy condition on the corresponding classical form. It is stated for windows with positive height floor and positive determinant floor, and is used to deduce the corresponding statement for arbitrary covering windows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (hk :
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ))
    (hk2 : ¬
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ (k - 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ)) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ ∧
        IsArchLoweringAnnihilatedAt w hw φ) := by sorry
