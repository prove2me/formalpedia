-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar
-- name    : AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/1d63832f-af61-5406-b577-ddd40aff33f4
-- title:
--   Smoothness and Casimir of a right convolution at a real place
-- statement:
--   Let $K$ be a number field all of whose infinite places are real, let $w$ be one of them, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, let $N$ be an ideal of $\mathcal{O}_K$, and let $\chi=(\chi_v)_v$ be a family of characters $\chi_v$ of the row-isometry subgroup at $v$ with values in $\mathbb{C}^\times$; write $U$ for the subgroup $\mathtt{levelOne}(N)\sqcap\ker(\mathtt{glArch})$ of $\mathrm{GL}_2(\mathbb{A}_K)$. Let $x'\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, right invariant under $U$ (membership in `levelInvariantSubmodule` for the pins built from $D$, the level groups $U$, the Hecke generators and the adelic box, only the level-group field of which is relevant), and of type $\chi_v$ at every infinite place $v$, i.e. in `archCutSubmodule` for the family `ArchTypeFamily.ofChar` of one-dimensional representations $\mathtt{charRep}(\chi_v)$. Let $\alpha$ be a factorizable test function (a product $f_\infty(\mathtt{glArch}\,g)f_{\mathrm{fin}}(\mathtt{glFin}\,g)$ with $f_\infty$ smooth in the archimedean matrix entries and compactly supported, $f_{\mathrm{fin}}$ locally constant and compactly supported) which is archimedean bi-finite for that family, and which satisfies $\alpha(kg)=\alpha(g)=\alpha(gk)$ for all $k\in U$. Put $x'*\alpha=\mathtt{rightConv}$, $(x'*\alpha)(g)=\int x'(gx)\alpha(x)\,d\mu(x)$ for the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$. The conclusion is fivefold: $x'*\alpha$ is smooth at $w$, in the sense that for every $g$ the function $e\mapsto (x'*\alpha)(g\cdot\mathtt{archRealLiftAt}\,e)$ is $C^\infty$ on the invertible real $2\times 2$ matrices; for each direction $d\in\{H,E,F\}$ the derivative $\mathtt{archDerivAt}\,d$ of $x'*\alpha$ along the corresponding one-parameter subgroup at $w$ is continuous; every iterated second derivative $\mathtt{archDerivAt}\,d\,(\mathtt{archDerivAt}\,d')$ of $x'*\alpha$ is continuous; there is a factorizable test function $\beta$, archimedean bi-finite for the same family, with $\Omega_w(x'*\alpha)=x'*\beta$, where $\Omega_w=-\bigl(\tfrac14 D_HD_H-\tfrac12 D_H+D_ED_F\bigr)$ is `archCasimirAt`; and $\Omega_w(x'*\alpha)$ is again right invariant under $U$ and of type $\chi_v$ at every infinite place.
--
--   This is the archimedean calculus of the smoothing operator $x'\mapsto x'*\alpha$ on adelic $\mathrm{GL}_2$: the convolution is smooth at a real place, has continuous derivatives up to order two, and the Casimir at that place is realised by convolution with a new test function of the same level and type. It is used in the construction of cuspidal constituents, where the Casimir eigenvalue and the type data are needed for functions obtained by smoothing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ))
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    IsArchSmoothAt hw (rightConv K x' α) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x' α))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x' α)))) ∧
    (∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsArchBiFinite K (ArchTypeFamily.ofChar K χ) β ∧
        archCasimirAt hw (rightConv K x' α) = rightConv K x' β) ∧
    archCasimirAt hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K (ArchTypeFamily.ofChar K χ) := by sorry
