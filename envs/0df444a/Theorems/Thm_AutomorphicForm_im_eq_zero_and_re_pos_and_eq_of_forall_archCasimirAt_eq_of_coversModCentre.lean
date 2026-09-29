-- Prove2me | Theorems.Thm_AutomorphicForm_im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre
-- name    : AutomorphicForm.im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d37f6aee-5831-5db2-93d8-3e61ad083d76
-- title:
--   Casimir scalar at a real place: reality, positivity, weight formula
-- statement:
--   Let $F$ be a number field, $c,u,d_1,d_2$ real numbers with $d_1<d_2$, and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, written $\mathrm{AdelicGL2}$; put $D=\bigcup_{x\in T}\{gx:g\in\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, where the centre-cut Siegel set consists of those $g$ whose finite part is integral, each of whose archimedean components has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$. Assume `CoversModCentre F D`: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,z\cdot 1\in D$. Let $\Theta$ be a complex Hecke eigensystem for $F$ (a nonzero level together with families $a,b$ indexed by the height-one primes of $\mathcal{O}_F$), let $w$ be a real infinite place with witness $hw$, and let $\mathrm{lam}\in\mathbb{C}$. Here `ArchOccursInClassOf F D Θ P` means that some eigensystem $\Theta'$ agreeing with $\Theta$ away from a finite set of primes admits a genuine smooth cuspidal realisation, for the production pins attached to $D$ (adelic Haar measure, the levels $\mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators, and the adelic box measure) and to $\Theta'.\mathrm{toRawCentral}$, whose underlying function satisfies $P$; `HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp …)` expresses that $\varphi$ transforms by the weight-$n$ character of the rotation subgroup at $w$, transported along the isomorphism $F_w\cong\mathbb{R}$; `IsArchSmoothAt hw φ` says that for each $g$ the function $e\mapsto\varphi(g\cdot\mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on the invertible real $2\times2$ matrices; and $\mathrm{archCasimirAt}\,hw$ is the operator $-\bigl(\tfrac14 H^2-\tfrac12 H+EF^-\bigr)$ formed from the one-parameter directional derivatives at $w$. Assume the rigidity hypothesis that for all $n\in\mathbb{Z}$ and $\mathrm{lam}'\in\mathbb{C}$, if the class of $\Theta$ over $D$ contains a witness of weight $n$ at $w$ which is arch-smooth and satisfies $\mathrm{archCasimirAt}\,hw\,\varphi=\mathrm{lam}'\cdot\varphi$, then $\mathrm{lam}'=\mathrm{lam}$. The conclusion is the conjunction of four assertions: if some weight $n$ occurs in the class, then $\mathrm{lam}$ is real; if weight $0$ occurs, then $\mathrm{lam}$ has positive real part; if weight $1$ occurs, then its real part is at least $1/4$; and if $k\ge 2$, weight $k$ occurs and weight $k-2$ does not, then $\mathrm{lam}=(k/2)(1-k/2)$.
--
--   This is the Bargmann-type determination of the archimedean parameter of a cuspidal Hecke class at a real place: reality and positivity of the Casimir scalar in the general case, and the discrete-series value $(k/2)(1-k/2)$ at a minimal $\mathrm{SO}(2)$-type $k\ge2$. It is an assembly of the rigidity of the Casimir scalar, the Bargmann bound, and the lowering-operator analysis, and it feeds the construction of the real archimedean parameter and Laplace eigenvalue used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm

theorem AutomorphicForm.im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (lam : ℂ)
    (hlam : ∀ (n : ℤ) (lam' : ℂ),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam' • φ) →
        lam' = lam) :
    (∀ n : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) →
        lam.im = 0) ∧
    (ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) →
        0 < lam.re) ∧
    (ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) →
        (1 / 4 : ℝ) ≤ lam.re) ∧
    (∀ k : ℤ, 2 ≤ k →
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) →
      ¬ ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ (k - 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) →
        lam = ((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) := by sorry
