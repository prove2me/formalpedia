-- Prove2me | Theorems.Thm_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
-- name    : AutomorphicForm.archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/6b035172-a7a4-5234-9ca6-95aa90d765da
-- title:
--   Shell-boundedness of derivatives of a Casimir eigen-witness at a real place
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite set of points of $\mathrm{GL}_2(\mathbb{A}_F)$; put $D=\bigcup_{x\in T}\{gx : g\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$. Assume `CoversModCentre F D`: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,z\in D$. Let $\Theta$ be a complex Hecke eigensystem over $F$ (a nonzero level ideal together with families $a_v,b_v$) and let $w$ be a real infinite place, $hw$ witnessing this. Then for every $n\in\mathbb Z$ and $\lambda\in\mathbb C$: if the class of $\Theta$ occurs over $D$ with a witness $\varphi$ satisfying (i) the predicate `HasArchCharacterAt₀` at $w$ for the character obtained by composing `archWeightCharℝ n` with the map of row-isometry subgroups induced by the real isomorphism attached to $hw$, which pins the archimedean type of $\varphi$ at $w$ to weight $n$, (ii) `IsArchSmoothAt hw`, i.e. for each $g$ the map $e\mapsto\varphi(g\cdot \mathrm{archRealLift}_w(e))$ is $C^\infty$ on invertible real $2\times2$ matrices, and (iii) $\Omega_w\varphi=\lambda\varphi$, where $\Omega_w=-\bigl(\tfrac14 D_H^2-\tfrac12 D_H+D_ED_{F^-}\bigr)$ and $D_d\varphi(g)=\frac{d}{dt}\varphi(g\,\mathrm{archFlow}_w(d,t))|_{t=0}$, then the class also occurs over $D$ with a witness satisfying (i), (ii), (iii) and in addition: for every finite list $l$ of directions in $\{H,E,F^-\}$ the iterated derivative $D_{l_1}\cdots D_{l_r}\varphi$ is continuous, and for all $0<e_1<e_2$ there is $B$ with $\|D_{l_1}\cdots D_{l_r}\varphi(g)\|\le B$ whenever the idele norm of $\det g$ lies in $[e_1,e_2]$. Here 'occurs over $D$' means `ArchOccursInClassOf`: there are a Hecke eigensystem $\Theta'$ agreeing with $\Theta$ away from a finite set of finite places and a smooth cusp realization $R'$ at the production pins of $D$ (with the level subgroups `levelOne ⊓ finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, and `adelicBox`) for $\Theta'$, genuine in the sense of `IsGenuineCuspRealizationAt`, whose underlying function satisfies the stated property.
--
--   This is the regularisation step for archimedean analysis of a cuspidal class on $\mathrm{GL}_2$ over $F$: a Casimir eigenvector of prescribed $\mathrm{SO}(2)$-weight at a real place may be replaced, within the same class, by one all of whose iterated Lie-algebra derivatives are continuous and bounded on each determinant shell, with the weight and the Casimir eigenvalue unchanged. It is used in the lower bound for the Casimir eigenvalue of lowering-annihilated vectors and in the weight-one Whittaker constructions of the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm

theorem AutomorphicForm.archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∀ (n : ℤ) (lam : ℂ),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = lam • φ) := by sorry
