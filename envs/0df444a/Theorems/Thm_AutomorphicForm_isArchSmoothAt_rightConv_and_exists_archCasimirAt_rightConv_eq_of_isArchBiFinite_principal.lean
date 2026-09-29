-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_principal
-- name    : AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/dbe93c3d-cb14-5e8b-9d7f-bc452b677958
-- title:
--   Casimir of a right convolution at principal level K(N)
-- statement:
--   Let $K$ be a number field, $D$ an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ a real infinite place of $K$, $N$ an ideal of $\mathcal{O}_K$, and $\mathrm{tys}$ an archimedean type family for $K$ (a number $\mathrm{card}(v)$ of types at each infinite place $v$ together with chosen archimedean representations $\mathrm{rep}(v,i)$). Let $x'\colon\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, right invariant under the subgroup $U(N)=\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$ (the level data of the pins built from $D$, this level family, the Hecke generators and the adelic box; only $U(N)$ enters the invariance condition), and lying in the archimedean cut $\bigsqcap_v\bigvee_i \mathrm{archTypeSubmoduleAt}(v,\mathrm{rep}(v,i))$. Let $\alpha$ be a factorizable test function, i.e. $\alpha(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ an archimedean and $f_{\mathrm{fin}}$ a finite test factor, which is archimedean bi-finite for $\mathrm{tys}$ (namely $g\mapsto\alpha(g^{-1})$ lies in the archimedean cut and $\alpha$ in the dual cut) and satisfies $\alpha(kg)=\alpha(g)=\alpha(gk)$ for all $k\in U(N)$. Then, with $\varphi=\mathrm{rightConv}(x',\alpha)$, $\varphi(g)=\int \varphi$-integrand $x'(gx)\alpha(x)\,d\mu(x)$ against adelic Haar measure: $\varphi$ is smooth at $w$ (for every $g$ the function $e\mapsto\varphi(g\cdot\mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on $\{\det e\neq0\}$); all first derivatives $\mathrm{archDerivAt}\,d\,\varphi$ and all second derivatives $\mathrm{archDerivAt}\,d\,(\mathrm{archDerivAt}\,d'\,\varphi)$, for $d,d'\in\{H,E,F\}$, are continuous; there exists a factorizable, archimedean bi-finite test function $\beta$ with $\mathrm{archCasimirAt}_w\varphi=\mathrm{rightConv}(x',\beta)$, where $\mathrm{archCasimirAt}_w=-\bigl(\tfrac14 D_HD_H-\tfrac12 D_H+D_ED_F\bigr)$; and $\mathrm{archCasimirAt}_w\varphi$ is again right $U(N)$-invariant and in the archimedean cut for $\mathrm{tys}$.
--
--   This is the archimedean calculus of a smoothing operator on adelic $\mathrm{GL}_2$ at principal level $K(N)$: right convolution by an admissible test function produces a function smooth at the chosen real place whose Casimir is again a convolution of the same function with a new admissible test function, so that the level and archimedean type conditions are preserved. It feeds the construction of smooth vectors inside cuspidal constituents, being used by [`AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut_principal`](thm.html#AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_archDerivAt_and_archCasimirAt_mem_of_mem_cut_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
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

theorem AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_principal
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K tys)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    IsArchSmoothAt hw (rightConv K x' α) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x' α))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x' α)))) ∧
    (∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧
        archCasimirAt hw (rightConv K x' α) = rightConv K x' β) ∧
    archCasimirAt hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K tys := by sorry
