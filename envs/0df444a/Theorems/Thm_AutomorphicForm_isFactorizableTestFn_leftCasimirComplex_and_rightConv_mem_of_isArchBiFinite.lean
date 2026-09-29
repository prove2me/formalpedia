-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite
-- name    : AutomorphicForm.isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e7a4c86e-cbf5-50a0-8b96-f6aef7b349f4
-- title:
--   Complex-place Casimirs of a factorizable test function: level and types
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ a complex infinite place of $K$, $N$ an ideal of $\mathcal{O}_K$, and $\mathrm{tys}$ an archimedean type family, i.e. a number $\mathrm{card}\,v$ of representations together with a choice of $\mathrm{card}\,v$ archimedean types for each infinite place $v$. Let $\alpha\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function, so $\alpha(g)=f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$; assume $\alpha$ is archimedean bi-finite of type $\mathrm{tys}$, i.e. $g\mapsto\alpha(g^{-1})$ lies in $\mathtt{archCutSubmodule}$ and $\alpha$ in $\mathtt{archDualCutSubmodule}$ for $\mathrm{tys}$, and that $\alpha(kg)=\alpha(g)=\alpha(gk)$ for all $k$ in the intersection of the level-$N$ subgroup $\mathtt{levelOne}$ with the kernel of the archimedean projection $\mathtt{glArch}$. Write $L_d\gamma(y)=\frac{d}{dt}\gamma\bigl(\mathtt{archFlowAtComplex}\,hw\,d\,(-t)\cdot y\bigr)\big|_{t=0}$ for the six directions $H,E,F^-,iH,iE,iF^-$ at $w$, and let $\beta$, $\bar\beta$ be the two explicit quadratic combinations $-\bigl(\tfrac1{16}(L_H\mp iL_{iH})^2-\tfrac14(L_H\mp iL_{iH})+\tfrac14(L_E\mp iL_{iE})(L_{F^-}\mp iL_{iF^-})\bigr)\alpha$, written out term by term with signs $-i$ for $\beta$ and $+i$ for $\bar\beta$. The assertion is fourfold: (i) $\beta$ and $\bar\beta$ are again factorizable test functions, archimedean bi-finite of type $\mathrm{tys}$; (ii) for every list $l$ of directions the iterated derivative $l.\mathtt{foldr}\,L\,\alpha$ is a factorizable test function; (iii) for every continuous $x'$ the right convolution $\mathtt{rightConv}\,K\,x'\,g=\int x'(g\cdot x)\,\cdot\,dx$ against $\beta$, resp. $\bar\beta$, equals the same combination, with the same coefficients, of the convolutions of $x'$ against the six or two-fold words $L_d(L_{d'}\alpha)$, $L_d\alpha$; and (iv) for every continuous $x'$ invariant on the right under $\mathtt{levelOne}\,N$ intersected with the kernel of $\mathtt{glArch}$ (this being membership in $\mathtt{levelInvariantSubmodule}$ at level $N$ for the pins $\mathtt{productionPinsOf}$ built from $D$, the subgroups $\mathtt{levelOne}\sqcap\ker\mathtt{glArch}$, the Hecke generators $\mathtt{heckeGen}$ and $\mathtt{adelicBox}$) and lying in $\mathtt{archCutSubmodule}$ for $\mathrm{tys}$, both $\mathtt{rightConv}\,K\,x'\,\beta$ and $\mathtt{rightConv}\,K\,x'\,\bar\beta$ again lie in the intersection of that level-invariant submodule with $\mathtt{archCutSubmodule}$.
--
--   This is the complex-place instance of the statement that the two Casimir elements of $\mathfrak{gl}_2(\mathbb{C})$, viewed as a real Lie algebra and acting through left translations, send an admissible factorizable test function to admissible factorizable test functions, and that smoothing a function by them preserves the level-$N$ right invariance and the prescribed archimedean types. It is used to identify the Casimir eigenvalue behaviour of right convolutions $x'\ast\alpha$, namely in the derivation that $x'\ast\beta$ and $x'\ast\bar\beta$ compute the archimedean Casimirs of $x'\ast\alpha$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDirComplex → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H (α)) y + ((-Complex.I) : ℂ) * L .H (L .iH (α)) y + ((-Complex.I) : ℂ) * L .iH (L .H (α)) y + (-1 : ℂ) * L .iH (L .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H (α) y + ((-Complex.I) : ℂ) * L .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm (α)) y + ((-Complex.I) : ℂ) * L .E (L .iFm (α)) y + ((-Complex.I) : ℂ) * L .iE (L .Fm (α)) y + (-1 : ℂ) * L .iE (L .iFm (α)) y))
    let βb : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H (α)) y + (Complex.I : ℂ) * L .H (L .iH (α)) y + (Complex.I : ℂ) * L .iH (L .H (α)) y + (-1 : ℂ) * L .iH (L .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H (α) y + (Complex.I : ℂ) * L .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm (α)) y + (Complex.I : ℂ) * L .E (L .iFm (α)) y + (Complex.I : ℂ) * L .iE (L .Fm (α)) y + (-1 : ℂ) * L .iE (L .iFm (α)) y))
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧ IsFactorizableTestFn K βb ∧ IsArchBiFinite K tys βb) ∧
    (∀ (l : List ArchDirComplex), IsFactorizableTestFn K (l.foldr L α)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      (rightConv K x' β = fun g =>
        -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (L .H (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .H (L .iH (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iH (L .H (α))) g + (-1 : ℂ) * rightConv K x' (L .iH (L .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (α)) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .E (L .Fm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .E (L .iFm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iE (L .Fm (α))) g + (-1 : ℂ) * rightConv K x' (L .iE (L .iFm (α))) g))) ∧
      (rightConv K x' βb = fun g =>
        -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (L .H (α))) g + (Complex.I : ℂ) * rightConv K x' (L .H (L .iH (α))) g + (Complex.I : ℂ) * rightConv K x' (L .iH (L .H (α))) g + (-1 : ℂ) * rightConv K x' (L .iH (L .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (α)) g + (Complex.I : ℂ) * rightConv K x' (L .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .E (L .Fm (α))) g + (Complex.I : ℂ) * rightConv K x' (L .E (L .iFm (α))) g + (Complex.I : ℂ) * rightConv K x' (L .iE (L .Fm (α))) g + (-1 : ℂ) * rightConv K x' (L .iE (L .iFm (α))) g)))) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
      rightConv K x' βb ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys) := by sorry
