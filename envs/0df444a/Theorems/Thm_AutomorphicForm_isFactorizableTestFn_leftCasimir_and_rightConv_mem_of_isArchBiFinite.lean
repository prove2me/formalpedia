-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite
-- name    : AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/d324d9e7-a973-55d9-8ee5-dac280dfca4a
-- title:
--   Left Casimir preserves test functions, types and level
-- statement:
--   Let $K$ be a number field, $D$ a set of points of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ a real infinite place of $K$ (witness `hw`), $N$ an ideal of $\mathcal{O}_K$, and `tys` an archimedean type family, i.e. for each infinite place a natural number together with that many archimedean representation types. Let $\alpha\colon\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function (it is the product of an archimedean test factor applied to `glArch` and a finite test factor applied to `glFin`), archimedean-bi-finite of type `tys` (that is, $y\mapsto\alpha(y^{-1})$ lies in `archCutSubmodule K tys` and $\alpha$ lies in `archDualCutSubmodule K tys`), and two-sided invariant under $U:=$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, i.e. $\alpha(kg)=\alpha(g)=\alpha(gk)$ for all $g$ and all $k\in U$. Write $(L_d\gamma)(y)=\frac{d}{dt}\big|_{t=0}\gamma\big(\mathrm{archFlowAt}\,hw\,d\,(-t)\cdot y\big)$ for $d\in\{H,E,F^-\}$, the left derivative along the split-torus, upper- and lower-unipotent one-parameter subgroups placed at $w$, and set $\beta=-\big(\tfrac14 L_HL_H\alpha-\tfrac12 L_H\alpha+L_EL_{F^-}\alpha\big)$. Then (1) $\beta$ is again a factorizable test function and is archimedean-bi-finite of type `tys`; (2) for every continuous $x'$, $\mathrm{rightConv}\,x'\,\beta=-\big(\tfrac14\,\mathrm{rightConv}\,x'\,(L_HL_H\alpha)-\tfrac12\,\mathrm{rightConv}\,x'\,(L_H\alpha)+\mathrm{rightConv}\,x'\,(L_EL_{F^-}\alpha)\big)$ pointwise; and (3) for every continuous $x'$ which is right $U$-invariant (membership in `levelInvariantSubmodule` at level $N$ for the pins `productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`) and lies in `archCutSubmodule K tys`, the convolution $\mathrm{rightConv}\,x'\,\beta$ again lies in the intersection of that level-invariant submodule with `archCutSubmodule K tys`.
--
--   This is the statement that smoothing by the Casimir element at a real place, applied to a test function through left translations, stays inside the admissible test functions and does not disturb the level structure or the archimedean types of the function being convolved; the underlying mechanism is the $\mathrm{Ad}$-invariance of the Casimir element of $U(\mathfrak{gl}_2)$. It is used in the construction of the Casimir action on adelic automorphic functions, via [`AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite`](thm.html#AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.lean

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

theorem AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ :=
      fun y => -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' β = fun g => -((1 / 4 : ℂ) * rightConv K x' (L .H (L .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (L .H α) g + rightConv K x' (L .E (L .Fm α)) g)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys) := by sorry
