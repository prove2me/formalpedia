-- Prove2me | Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre
-- name    : AutomorphicForm.archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/30ff73e5-a7dc-51ec-b23a-97659d98a651
-- title:
--   Weight-zero occurrence can be taken J-eigen at a real place
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$; write $D=\bigcup_{x\in T}\{gx : g\in\mathcal S\}$ for the union of the right translates by the elements of $T$ of the centre-cut Siegel set $\mathcal S=$ `centreCutSiegelSet F c u d₁ d₂` (finite part integral, all archimedean local heights at least $c$, all archimedean $x$-window squares at most $u^2$, all archimedean determinant norms in $[d_1,d_2]$). Assume `CoversModCentre F D`: every $g\in\mathrm{GL}_2(\mathbb A_F)$ has $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g z\in D$. Let $\Theta$ be a complex Hecke eigensystem for $F$ (a level ideal $\neq\bot$ together with families $a,b$ indexed by the height-one primes of $\mathcal O_F$), let $w$ be a real infinite place with witness $hw$, and let $\lambda,e\in\mathbb C$. The hypothesis is that the property $P$ occurs in the class of $D$ and $\Theta$ in the sense of `ArchOccursInClassOf`, i.e. there are a Hecke eigensystem $\Theta'$ agreeing with $\Theta$ away from a finite set and a genuine smooth cuspidal realization $R'$ at the production pins of $D$ (level-one-meet-finite-adelic subgroups, the Hecke generators, the adelic box) for the central datum of $\Theta'$, whose underlying function $\varphi=R'.\mathrm{toFun}$ satisfies: $\varphi$ has archimedean character at $w$ in the sense of `HasArchCharacterAt₀` for the character `archWeightCharℝ 0` composed with `rowIsometrySubgroup₀Map` along the isomorphism $F_w\cong\mathbb R$ attached to $hw$; $\varphi$ is smooth at $w$, meaning that for each $g$ the function $e\mapsto\varphi(g\cdot\mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on the invertible real $2\times2$ matrices; for every list $l$ of directions drawn from $H,E,F^-$ the iterated flow derivative $l$-fold `archDerivAt hw` of $\varphi$ (each step the derivative at $t=0$ of $t\mapsto\varphi(g\cdot\mathrm{archFlowAt}\,hw\,d\,t)$) is continuous and, for all $0<e_1<e_2$, bounded on the shell where the idele norm of $\det g$ lies in $[e_1,e_2]$; $\mathrm{archCasimirAt}\,hw\,\varphi=-\big(\tfrac14 H^2-\tfrac12 H+EF^-\big)\varphi=\lambda\varphi$; and $\varphi(\iota_w(t\cdot I)g)=t^{e}\varphi(g)$ for every real unit $t>0$, where $\iota_w$ is the inclusion of $\mathrm{GL}_2(F_w)$ and $t$ is transported through $F_w\cong\mathbb R$. The conclusion is that the conjunction of $P$ with the further condition "there is $\varepsilon\in\mathbb C$ with $\varepsilon=1$ or $\varepsilon=-1$ such that $\varphi(g\cdot\mathrm{archRealGLAt}\,hw\,J)=\varepsilon\,\varphi(g)$ for all $g$", with $J=$ `UpperHalfPlane.J` in $\mathrm{GL}_2(\mathbb R)$ mapped into $\mathrm{GL}_2(\mathbb A_F)$ at $w$, also occurs in the class of $D$ and $\Theta$.
--
--   This is the normalisation step in the archimedean analysis at a real place which replaces a weight-zero Casimir eigenfunction occurring in the class of a Siegel covering by one that is in addition an eigenvector, with sign $\pm1$, for right translation by the reflection $J$ in $\mathrm{GL}_2(F_w)$. It is used in the Langlands–Tunnell converse-theorem input, where the $J$-sign determines the shape of the archimedean Whittaker coefficient of the realization.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem AutomorphicForm.archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (lam e : ℂ)
    (hocc : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = lam • φ ∧
            (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g))) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => (HasArchCharacterAt₀ F w ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = lam • φ ∧
            (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g)) ∧
          ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
            ∀ g : AdelicGL2 (𝓞 F) F, φ (g * archRealGLAt hw UpperHalfPlane.J) = ε * φ g) := by sorry
