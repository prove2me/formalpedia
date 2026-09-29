-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite
-- name    : AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/e0f43e2e-8597-527f-9956-eb14a4f1c768
-- title:
--   Casimir action on a smoothing at a complex place
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ an infinite place of $K$ assumed complex, $N$ an ideal of $\mathcal{O}_K$ and $\mathrm{tys}$ an archimedean type family, i.e. for each infinite place $v$ a finite list $\mathrm{tys}.\mathrm{rep}\,v$ of representations of the row-isometry subgroup at $v$. Let $x' : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, right invariant under the group $U(N) = \mathrm{levelOne}(N) \cap \ker(\mathrm{glArch})$ that the carrier pins `productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)` assign to $N$, and lying in `archCutSubmodule K tys`, the intersection over all infinite places $v$ of the sum of the type submodules attached to the representations $\mathrm{tys}.\mathrm{rep}\,v\,i$. Let $\alpha$ be a factorizable test function, that is a product of a smooth compactly supported function of the archimedean matrix entries with a locally constant compactly supported function of the finite part; assume $\alpha$ is archimedean bi-finite for $\mathrm{tys}$, meaning $g \mapsto \alpha(g^{-1})$ lies in `archCutSubmodule K tys` and $\alpha$ lies in `archDualCutSubmodule K tys`, and that $\alpha(kg) = \alpha(g) = \alpha(gk)$ for all $g$ and all $k \in U(N)$. Write $x' * \alpha$ for `rightConv K x' α`, the integral $g \mapsto \int x'(gx)\,\alpha(x)$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$. Then: $x' * \alpha$ is smooth at $w$, in the sense that for every $g$ the function $e \mapsto (x'*\alpha)(g \cdot \mathrm{archComplexLiftAt}\,hw\,e)$ is $C^\infty$ on the set of $e \in M_2(\mathbb{C})$ with $\det e \neq 0$; for each of the six flow directions $d$ the derivative $\mathrm{archDerivAtComplex}\,hw\,d\,(x'*\alpha)$ is continuous, and so is every iterated derivative along two directions $d, d'$; there exist factorizable test functions $\beta$ and $\beta_b$, both archimedean bi-finite for $\mathrm{tys}$, with $\mathrm{archCasimirAtComplex}\,hw\,(x'*\alpha) = x' * \beta$ and $\mathrm{archCasimirBarAtComplex}\,hw\,(x'*\alpha) = x' * \beta_b$; and both $\mathrm{archCasimirAtComplex}\,hw\,(x'*\alpha)$ and $\mathrm{archCasimirBarAtComplex}\,hw\,(x'*\alpha)$ again lie in the intersection of the level-$N$ invariant submodule for these pins with `archCutSubmodule K tys`.
--
--   This is the complex-place instance of the principle that convolution on the right by a test function smooths an automorphic function and that the holomorphic and antiholomorphic Casimir operators of $\mathrm{GL}_2(\mathbb{C})$ act on the smoothing through corresponding left-invariant Casimir operators applied to the test function, which remains a factorizable bi-finite test function. It is what makes the level-and-type cut of a cuspidal constituent stable under both Casimir operators, and it is used in [`AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut`](thm.html#AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite.lean

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

theorem AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K tys)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    IsArchSmoothAtComplex hw (rightConv K x' α) ∧
    (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x' α))) ∧
    (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x' α)))) ∧
    (∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧
        archCasimirAtComplex hw (rightConv K x' α) = rightConv K x' β) ∧
    (∃ βb : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K βb ∧ IsArchBiFinite K tys βb ∧
        archCasimirBarAtComplex hw (rightConv K x' α) = rightConv K x' βb) ∧
    archCasimirAtComplex hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K tys ∧
    archCasimirBarAtComplex hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K tys := by sorry
