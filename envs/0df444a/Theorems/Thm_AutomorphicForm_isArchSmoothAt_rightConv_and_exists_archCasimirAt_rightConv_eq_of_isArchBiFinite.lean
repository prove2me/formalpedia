-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite
-- name    : AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/99649e23-4633-5e5c-b9df-7459c0a9ed2d
-- title:
--   Casimir at a real place of a right convolution
-- statement:
--   Let $K$ be a number field, $D$ an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ a real infinite place of $K$, $N$ an ideal of $\mathcal{O}_K$ and $\mathrm{tys}$ an `ArchTypeFamily` for $K$, i.e. a finite list $\mathrm{rep}\,w\,i$ ($i<\mathrm{card}\,w$) of archimedean types at each infinite place $w$. Let $x' : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, lie in `archCutSubmodule` for $\mathrm{tys}$ (the infimum over infinite places of the supremum of the type submodules attached to the listed types), and satisfy $x'(gu)=x'(g)$ for all $g$ and all $u$ in $U_1(N)\cap\ker(\mathrm{gl}_{\mathrm{Arch}})$, the latter being the level group carved out by `productionPinsOf` at $N$. Let $\alpha : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function (a product of an archimedean and a finite test factor through $\mathrm{gl}_{\mathrm{Arch}}$ and $\mathrm{gl}_{\mathrm{Fin}}$), be `IsArchBiFinite` for $\mathrm{tys}$ ($y\mapsto\alpha(y^{-1})$ lies in `archCutSubmodule` and $\alpha$ in `archDualCutSubmodule`), and satisfy $\alpha(kg)=\alpha(g)=\alpha(gk)$ for $k$ in that same level group. Then the right convolution $\mathrm{rightConv}\,K\,x'\,\alpha$, $g\mapsto\int x'(gx)\alpha(x)\,dx$ against adelic Haar measure, is archimedean-smooth at $w$ in the sense of `IsArchSmoothAt` (smooth in the real matrix entries lifted at $w$, on the locus of nonzero determinant, at every base point); all its first derivatives $\mathrm{archDerivAt}\,hw\,d$ and all second derivatives $\mathrm{archDerivAt}\,hw\,d\,(\mathrm{archDerivAt}\,hw\,d')$ along the directions $d,d'\in\{H,E,F\}$ are continuous; there exists a factorizable, `IsArchBiFinite` test function $\beta$ with $\mathrm{archCasimirAt}\,hw\,(x'*\alpha)=x'*\beta$, where $\mathrm{archCasimirAt}$ is $-\bigl(\tfrac14 D_HD_H-\tfrac12 D_H+D_ED_F\bigr)$; and $\mathrm{archCasimirAt}\,hw\,(x'*\alpha)$ again lies in the level-$N$ right-invariance submodule and in `archCutSubmodule` for $\mathrm{tys}$.
--
--   This is the statement that the smoothing operator given by right convolution with an archimedean-bi-finite factorizable test function produces vectors on which the Casimir element at a real place acts again through convolution, preserving level and archimedean type. It is used in the construction of cuspidal constituents, via [`AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut`](thm.html#AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite.lean

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

theorem AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K tys)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    IsArchSmoothAt hw (rightConv K x' α) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x' α))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x' α)))) ∧
    (∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧
        archCasimirAt hw (rightConv K x' α) = rightConv K x' β) ∧
    archCasimirAt hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K tys := by sorry
