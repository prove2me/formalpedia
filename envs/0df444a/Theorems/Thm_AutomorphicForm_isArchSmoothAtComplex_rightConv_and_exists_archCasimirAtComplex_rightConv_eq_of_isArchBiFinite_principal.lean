-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite_principal
-- name    : AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/4a228b85-30fe-57de-841b-7ec7452f1c4f
-- title:
--   Casimirs of a right convolution at a complex place, principal level
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ an infinite place of $K$ with $w$ complex, $N$ an ideal of $\mathcal{O}_K$ and $\mathrm{tys}$ an archimedean type family on $K$ (a finite list of representations of the row-isometry subgroup at each infinite place). Let $x' : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, right invariant under the subgroup $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$ (that is, $x'(gu)=x'(g)$ for all $g$ and all such $u$; the level data are those of `productionPinsOf` with level family $N\mapsto\mathrm{principalLevel}(N)\cap\mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $\mathrm{heckeGen}$ and box $\mathrm{adelicBox}$), and lying in $\mathrm{archCutSubmodule}\,\mathrm{tys}$, the intersection over infinite places of the sums of the type submodules attached to $\mathrm{tys}$. Let $\alpha$ be a factorizable test function (a product of a compactly supported smooth archimedean factor and a compactly supported locally constant finite factor), arch bi-finite for $\mathrm{tys}$ (i.e. $g\mapsto\alpha(g^{-1})$ lies in $\mathrm{archCutSubmodule}\,\mathrm{tys}$ and $\alpha$ in $\mathrm{archDualCutSubmodule}\,\mathrm{tys}$), and invariant on both sides under that same subgroup. Write $x'\ast\alpha$ for $g\mapsto\int x'(gx)\alpha(x)\,dx$ against adelic Haar measure. Then: $x'\ast\alpha$ is smooth at $w$, in the sense that for every $g$ the function $e\mapsto (x'\ast\alpha)(g\cdot\mathrm{archComplexLiftAt}\,e)$ is $C^\infty$ on the set of $2\times2$ complex matrices of nonzero determinant; all first and all second derivatives $\mathrm{archDerivAtComplex}$ of $x'\ast\alpha$ along the six directions $H,E,F,iH,iE,iF$ are continuous; there exist factorizable, arch bi-finite test functions $\beta$ and $\bar\beta$ with $\Omega_w(x'\ast\alpha)=x'\ast\beta$ and $\bar\Omega_w(x'\ast\alpha)=x'\ast\bar\beta$, where $\Omega_w=\mathrm{archCasimirAtComplex}$ and $\bar\Omega_w=\mathrm{archCasimirBarAtComplex}$ are the quadratic expressions in the holomorphic, respectively antiholomorphic, half-derivatives; and both $\Omega_w(x'\ast\alpha)$ and $\bar\Omega_w(x'\ast\alpha)$ again lie in the intersection of the level-invariant submodule for $N$ and $\mathrm{archCutSubmodule}\,\mathrm{tys}$.
--
--   This is the smoothing step at a complex place in the archimedean analysis of adelic automorphic functions: convolution on the right by a factorizable test function produces a function smooth at $w$ whose Casimir and conjugate Casimir images are again convolutions of $x'$ with test functions of the same kind, so that the level and type conditions are preserved. It is the variant for the principal congruence level $\mathrm{principalLevel}(N)$ met with the finite-adelic subgroup, and feeds the corresponding statement for members of the archimedean cut submodule, [`AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut_principal`](thm.html#AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite_principal
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K tys)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    IsArchSmoothAtComplex hw (rightConv K x' α) ∧
    (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x' α))) ∧
    (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x' α)))) ∧
    (∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧
        archCasimirAtComplex hw (rightConv K x' α) = rightConv K x' β) ∧
    (∃ βb : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K βb ∧ IsArchBiFinite K tys βb ∧
        archCasimirBarAtComplex hw (rightConv K x' α) = rightConv K x' βb) ∧
    archCasimirAtComplex hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K tys ∧
    archCasimirBarAtComplex hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K tys := by sorry
