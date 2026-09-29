-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf
-- name    : AutomorphicForm.exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e6bb45e9-4bd1-5e38-b471-00c148a8d97a
-- title:
--   Occurring weight-one type lies in one cuspidal constituent
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$; write $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, and assume `CoversModCentre F D`, i.e. every $g\in \mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^{\times}$ with $\gamma g z\in D$. Let $\Theta$ be a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a,b$ indexed by the finite places), $w$ a real infinite place, and $P$ an arbitrary predicate on functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$. Throughout, pins means `productionPinsOf F D` with level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\mathrm{finiteAdelicGL2Subgroup}$, Hecke elements `heckeGen`, and conditioning box `adelicBox F`. The hypothesis `ArchOccursInClassOf` for $D$, $\Theta$ and the predicate "$\varphi$ satisfies `HasArchCharacterAt₀` at $w$ for the character `archWeightCharℝ 1` pulled back along `rowIsometrySubgroup₀Map` through the identification of $w$'s completion with $\mathbb{R}$, and $P\,\varphi$" provides some eigensystem agreeing with $\Theta$ outside a finite set of primes together with a continuous smooth cusp realization at the pins whose function has that weight-one behaviour at $w$ and satisfies $P$. The conclusion asserts the existence of an eigensystem $\Theta'$ agreeing with $\Theta$ away from a finite set of primes, a smooth cusp realization $R'$ at the pins for $\Theta'.\mathrm{toRawCentral}$ (the eigensystem with $b$ divided by the residue norms) with $R'.\mathrm{toFun}$ continuous and satisfying $P$, and furthermore a finite set $S$ of finite places containing $R'.\mathrm{exceptionalSet}$, an archimedean type family $\mathrm{tys}$, a submodule $V\subseteq(\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C})$ and a function $x_0$ such that: $V$ is a cuspidal constituent for the central character $R'.\mathrm{centralChar}$ (a nonzero cuspidal $K$-finite subrepresentation stable under the finite adelic group, the archimedean row-isometry subgroups and right convolution by factorizable archimedean bi-finite test functions, minimal among such); $x_0\neq 0$, $x_0\in V$; $x_0$ lies in the span of the isotypic cusp forms at the pins for $R'.\mathrm{centralChar}$, level $\Theta'.\mathrm{level}$, exceptional set $S$ and eigensystem $\Theta'$; $x_0$ lies in $\mathrm{archCutSubmodule}\,\mathrm{tys}$, the intersection over all infinite places of the sums of the type submodules listed by $\mathrm{tys}$; the list $\mathrm{tys}.\mathrm{rep}\,w$ contains both `ArchRepAt.ofChar` of the weight $1$ and of the weight $-1$ character at $w$; $x_0$ satisfies `HasArchCharacterAt₀` at $w$ for the weight $1$ character; $x_0$ is archimedean-smooth at $w$ in the sense of `IsArchSmoothAt hw`; and for every list $l$ of directions in $\{H,E,F^-\}$ the iterated derivative $l.\mathrm{foldr}\,(\mathrm{archDerivAt}\,hw)\,x_0$ is continuous and, for all $0<e_1<e_2$, bounded in absolute value on the shell of $g$ with $\|\det g\|_{\mathbb{A}_F}\in[e_1,e_2]$.
--
--   This packages an archimedean weight-one occurrence in a Hecke class into a single irreducible cuspidal constituent containing a nonzero vector of that type, with both weights $\pm1$ admitted by the archimedean cut so that the Weyl element at $w$ acts inside it, and with the growth and smoothness data needed for Casimir computations. It feeds the rigidity step [`AutomorphicForm.archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat`](thm.html#AutomorphicForm.archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat), and is obtained from the right-convolution construction, the isotypic-cut dictionary and strong multiplicity one for cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop)
    (hocc : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ P φ)) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
    ∃ R' : SmoothCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ'.toRawCentral,
      IsGenuineCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ'.toRawCentral R' ∧ P R'.toFun ∧
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F)
      (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (x₀ : AdelicGL2 (𝓞 F) F → ℂ),
      R'.exceptionalSet ⊆ S ∧
      IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar V ∧
      x₀ ≠ 0 ∧ x₀ ∈ V ∧
      x₀ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar Θ'.level S Θ' ∧
      x₀ ∈ archCutSubmodule F tys ∧
      (∃ i, tys.rep w i = ArchRepAt.ofChar F ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))) ∧
      (∃ i, tys.rep w i = ArchRepAt.ofChar F ((archWeightCharℝ (-1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))) ∧
      HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) x₀ ∧
      IsArchSmoothAt hw x₀ ∧
      (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) x₀) ∧
        ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
            ‖l.foldr (archDerivAt hw) x₀ g‖ ≤ B) := by sorry
