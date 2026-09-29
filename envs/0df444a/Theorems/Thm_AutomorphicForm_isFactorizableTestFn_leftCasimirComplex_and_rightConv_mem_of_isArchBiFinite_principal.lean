-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite_principal
-- name    : AutomorphicForm.isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/512840f5-fd52-5d86-b17b-6fb9c0a6a724
-- title:
--   Left Casimirs at a complex place preserve level and types
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ a complex infinite place of $K$, $N$ an ideal of $\mathcal{O}_K$, and $\mathrm{tys}$ a family assigning to each infinite place a finite list of archimedean types. Let $\alpha:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be factorizable, i.e. $\alpha(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$; assume $\alpha$ is archimedean bi-finite of type $\mathrm{tys}$, meaning $y\mapsto\alpha(y^{-1})$ lies in $\bigsqcap_{w'}\bigsqcup_i$ of the type submodules at $w'$ and $\alpha$ lies in the dual cut submodule; and assume $\alpha(kg)=\alpha(g)=\alpha(gk)$ for all $g$ and all $k$ in the intersection of the principal level subgroup $K(N)$ with the kernel of the archimedean projection. For $d$ among the six directions $H,E,F^-,iH,iE,iF^-$ put $(L_d\gamma)(y)=\frac{d}{dt}\gamma(\mathrm{flow}_d(-t)\,y)|_{t=0}$, the flows being the images at $w$ of the split torus, upper and lower unipotent one-parameter subgroups of $\mathrm{GL}_2(\mathbb{C})$, with or without a factor $i$. Let $$\beta=-\Bigl(\tfrac14\bigl(\tfrac14(L_HL_H-iL_HL_{iH}-iL_{iH}L_H-L_{iH}L_{iH})\alpha\bigr)-\tfrac12\bigl(\tfrac12(L_H-iL_{iH})\alpha\bigr)+\tfrac14(L_EL_{F^-}-iL_EL_{iF^-}-iL_{iE}L_{F^-}-L_{iE}L_{iF^-})\alpha\Bigr)$$ and let $\bar\beta$ be the same expression with $i$ in place of $-i$ throughout. The conclusion is fourfold: (i) $\beta$ and $\bar\beta$ are again factorizable test functions and archimedean bi-finite of type $\mathrm{tys}$; (ii) for every finite word $l$ in the six directions, $L_{l_1}\cdots L_{l_k}\alpha$ is a factorizable test function; (iii) for every continuous $x'$, the right convolutions $\mathrm{rightConv}\,x'\,\beta$ and $\mathrm{rightConv}\,x'\,\bar\beta$, where $\mathrm{rightConv}\,x'\,f(g)=\int x'(gx)f(x)\,d\mu(x)$ for adelic Haar measure $\mu$, equal the corresponding linear combinations of the convolutions of $x'$ against the individual words above; and (iv) for every continuous $x'$ satisfying $x'(gu)=x'(g)$ for all $u$ in that same level group, as prescribed by the pins built from $D$, the level family $N\mapsto K(N)$ intersected with the finite-adelic subgroup, the local Hecke generators and the adelic box, and lying in the archimedean cut submodule of type $\mathrm{tys}$, both $\mathrm{rightConv}\,x'\,\beta$ and $\mathrm{rightConv}\,x'\,\bar\beta$ again lie in the intersection of that level-invariant submodule with the archimedean cut submodule.
--
--   This is the statement that the two left Casimir operators at a complex place act on admissible factorizable test functions without destroying factorizability, archimedean bi-finiteness, level invariance or archimedean type, and that Casimir smoothing commutes with right convolution; it is the version for the principal congruence level $K(N)$. It feeds the construction of archimedean smoothness and Casimir relations for convolutions, being cited by [`AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite_principal`](thm.html#AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite_principal.lean

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

theorem AutomorphicForm.isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite_principal
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
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
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
      rightConv K x' βb ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys) := by sorry
