-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
-- name    : AutomorphicForm.exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/dbcd4ae4-d6ee-5d12-92a5-8ed6953fe41b
-- title:
--   Casimir scalar at a real place: rigidity and regular witnesses
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$ (the adelic general linear group over $\mathcal O_F\subset F$). Put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in the integral part of the finite adelic group, whose archimedean components have local height $\ge c$ at every infinite place, $x$-window square $\le u^2$ at every infinite place, and archimedean determinant norm in $[d_1,d_2]$ at every infinite place. Assume `CoversModCentre F D`: every $g\in\mathrm{GL}_2(\mathbb A_F)$ can be written with $\gamma\in\mathrm{GL}_2(F)$ and a central idelic scalar $z$ so that $\gamma g z\in D$. Let $\Theta$ be a Hecke eigensystem over $F$ with complex values (a nonzero level ideal together with families $a,b$ indexed by the height-one primes of $\mathcal O_F$), and let $w$ be a real infinite place, with $hw$ witnessing $w.\mathrm{IsReal}$. Throughout, `ArchOccursInClassOf F D Θ P` means: there is a Hecke eigensystem $\Theta'$ agreeing with $\Theta$ away from finitely many places and a smooth cusp realisation $R'$ at the production pins of $D$ (levels `levelOne ⊓ finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, the adelic box) for the raw central datum of $\Theta'$, which is a genuine cusp realisation, such that $P$ holds of the function of $R'$. The conclusion asserts the existence of $\lambda\in\mathbb C$ with two properties. First, rigidity: for every $n\in\mathbb Z$ and every $\lambda'\in\mathbb C$, if there occurs in the class of $\Theta$ over $D$ a function $\varphi$ satisfying the weight-$n$ archimedean character condition `HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map …))` at $w$ transported along the isomorphism $F_w\cong\mathbb R$, satisfying `IsArchSmoothAt hw φ` (i.e. $e\mapsto\varphi(g\cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the locus $\det e\ne 0$, for every $g$), and satisfying $\Omega_w\varphi=\lambda'\varphi$ for the Casimir operator $\Omega_w=\mathrm{archCasimirAt}\,hw=-\bigl(\tfrac14 H^2-\tfrac12 H+EF\bigr)$ built from the derivatives at $t=0$ of right translation along the three one-parameter flows $H,E,F$ at $w$, then $\lambda'=\lambda$. Second, regular eigenwitnesses: for every $n\in\mathbb Z$, if some function of weight $n$ at $w$ occurs in the class, then one occurs which in addition is smooth at $w$, has every iterated derivative $\mathrm{archDerivAt}$ along an arbitrary finite list of the three directions continuous and bounded on each determinant shell (for all $0<e_1<e_2$ there is $B$ with $\|\cdot\|\le B$ on all $g$ whose idele norm of $\det g$ lies in $[e_1,e_2]$), and satisfies $\Omega_w\varphi=\lambda\varphi$ with the same $\lambda$. Only $d_1<d_2$ is assumed; no positivity of $c$ or $d_1$ is required.
--
--   This attaches to a near-equivalence class of Hecke eigensystems a single Casimir (Laplace) eigenvalue at a chosen real place, and simultaneously provides, in each occurring $\mathrm{SO}(2)$-weight, a witness that is smooth at $w$, has all iterated archimedean derivatives continuous and bounded on determinant shells, and is a Casimir eigenfunction for that eigenvalue. It is the archimedean input for the subsequent analysis of weights and of the $J$-symmetry of class witnesses, and for the reformulation of occurrence in terms of the Casimir eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ lam : ℂ,
      (∀ (n : ℤ) (lam' : ℂ),
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
              IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam' • φ) →
          lam' = lam) ∧
      (∀ n : ℤ,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) →
          ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
              IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
              archCasimirAt hw φ = lam • φ)) := by sorry
