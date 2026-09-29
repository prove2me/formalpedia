-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/edf8cf22-35bf-5a44-baf8-7c07629704b6
-- title:
--   Archimedean smoothing of a cuspidal realisation at a real place
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$ such that the set $D=\bigcup_{x\in T}\{gx : g\in \mathrm{centreCutSiegelSet}\}$ satisfies `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb A_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and a central idele scalar $z$ with $\gamma g z\in D$. Let $\Theta$ be a complex Hecke eigensystem over $F$ (a nonzero level ideal together with families $a,b$ indexed by the finite places), and let $R$ be a `SmoothCuspRealizationAt` for the production pins of $D$ — Haar measure and the Borel structure on $\mathrm{GL}_2(\mathbb A_F)$, fundamental set $D$, full central subgroup, level groups $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, Hecke elements $\mathrm{heckeGen}\,v$, and the adelic box as conditioning set — for the eigensystem $\Theta.\mathrm{toRawCentral}$, which has the same level and same $a$ and central eigenvalues $b_v$ divided by $\#(\mathcal O_F/v)$; thus $R$ provides a nonzero function $\varphi=R.\mathrm{toFun}$, a central character $\xi=R.\mathrm{centralChar}$, smoothness and cuspidality at those pins, invariance under the level subgroup at $\Theta.\mathrm{level}$, and, outside a finite exceptional set $S_0=R.\mathrm{exceptionalSet}$, the Hecke coset eigen-equations with eigenvalue $a_v$ and the central eigen-equations. Assume $\varphi$ continuous. Let $w$ be a real place of $F$, $n\in\mathbb Z$, and assume `HasArchCharacterAt₀` at $w$ for $\varphi$ with respect to the character obtained from `archWeightCharℝ n` by transporting along the isomorphism of $F_w$ with $\mathbb R$, i.e. right translation by the identity-component rotation subgroup at $w$ multiplies $\varphi$ by that weight-$n$ character. Then there are a finite set $S$ of finite places with $S_0\subseteq S$, an archimedean type family $\mathrm{tys}$ (for each infinite place finitely many finite-dimensional representations of the identity component of the row-isometry subgroup there), and $f:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ such that: $f$ is factorizable, being a product of an archimedean factor that is a smooth function of the matrix entries with compact support and a locally constant compactly supported factor on the finite adeles; $f$ is arch-bi-finite for $\mathrm{tys}$, meaning $x\mapsto f(x^{-1})$ lies in `archCutSubmodule` and $f$ in `archDualCutSubmodule`; and the right convolution $\varphi*f:g\mapsto\int \varphi(gx)f(x)\,dx$ against adelic Haar measure is nonzero, lies in the isotypic cuspidal submodule for these pins with data $(\xi,\Theta.\mathrm{level},S,\Theta)$ (the span of continuous smooth cuspidal automorphic functions invariant under the level subgroup which, outside $S$, are Hecke eigenfunctions with eigenvalues $\Theta.a_v$ and central eigenfunctions with eigenvalues of $\Theta.\mathrm{toRawCentral}.b_v$), lies in `archCutSubmodule` for $\mathrm{tys}$, satisfies the same weight-$n$ character condition at $w$, is `IsArchSmoothAt` for $w$ (infinitely differentiable along the real lift of invertible $2\times2$ real matrices at $w$), and for every finite list $l$ of directions in $\{H,E,F^-\}$ the iterated derivative of $\varphi*f$ along the corresponding one-parameter flows at $w$ is continuous and, for all $0<e_1<e_2$, bounded on $\{g:\ \lVert\det g\rVert_{\mathbb A}\in[e_1,e_2]\}$.
--
--   This is the archimedean smoothing (Gårding-vector / $K$-finite smoothing) step: a merely continuous cuspidal Hecke eigenrealisation is replaced by a nonzero convolution against a factorizable test function, which is smooth at a chosen real place, of finite archimedean type, and of controlled growth on determinant shells, while retaining the Hecke and central eigenvalue data and the weight at $w$. It feeds the subsequent results identifying the Casimir action at the real place on such smoothed forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ)
    (hn : HasArchCharacterAt₀ F w
      ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ),
      R.exceptionalSet ⊆ S ∧ IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
      rightConv F R.toFun f ≠ 0 ∧
      rightConv F R.toFun f ∈ isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
        R.centralChar Θ.level S Θ ∧
      rightConv F R.toFun f ∈ archCutSubmodule F tys ∧
      HasArchCharacterAt₀ F w
        ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) (rightConv F R.toFun f) ∧
      IsArchSmoothAt hw (rightConv F R.toFun f) ∧
      (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) (rightConv F R.toFun f)) ∧
        ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
            ‖l.foldr (archDerivAt hw) (rightConv F R.toFun f) g‖ ≤ B) := by sorry
