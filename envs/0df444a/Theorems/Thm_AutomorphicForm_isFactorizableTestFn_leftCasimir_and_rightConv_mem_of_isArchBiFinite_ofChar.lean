-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar
-- name    : AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0e7ed60d-613e-5978-8364-b32189dfa445
-- title:
--   Casimir of a test function: level and archimedean type
-- statement:
--   Let $K$ be a totally real number field, in the sense that every infinite place of $K$ is real, let $w$ be a real place of $K$, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, let $N$ be an ideal of $\mathcal{O}_K$, and let $\chi=(\chi_v)_v$ assign to each infinite place $v$ a character $\chi_v$ of the group of row isometries of $K_v$ with values in $\mathbb{C}^\times$. Let $\alpha:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function, i.e. $\alpha(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ the restriction of a $C^\infty$ function of the archimedean matrix entries and compactly supported, and $f_{\mathrm{fin}}$ locally constant with compact support; assume $\alpha$ is archimedean bi-finite for the type family made of the one-dimensional representations attached to the $\chi_v$, that is, $x\mapsto\alpha(x^{-1})$ lies in the archimedean cut submodule and $\alpha$ in the archimedean dual cut submodule of that family; and assume $\alpha(kg)=\alpha(g)=\alpha(gk)$ for all $g$ and all $k$ in the intersection of the level-one subgroup of $N$ with the kernel of the archimedean projection $\mathrm{glArch}$. Write $(L_d\gamma)(y)=\frac{d}{dt}\big|_{t=0}\gamma(\mathrm{archFlowAt}\,hw\,d\,(-t)\cdot y)$ for the left derivative along the one-parameter flow placed at $w$ in direction $d\in\{H,E,F^-\}$ (split torus, upper and lower unipotent), and set $\beta=-\big(\tfrac14 L_HL_H\alpha-\tfrac12 L_H\alpha+L_EL_{F^-}\alpha\big)$. Then: (1) $\beta$ is again a factorizable test function and is archimedean bi-finite for the same character family; (2) for every continuous $x'$ the right convolution $g\mapsto\int x'(gx)\beta(x)\,d\mu(x)$ against adelic Haar measure equals $-\big(\tfrac14\,x'*L_HL_H\alpha-\tfrac12\,x'*L_H\alpha+x'*L_EL_{F^-}\alpha\big)$; and (3) for every continuous $x'$ with $x'(gu)=x'(g)$ for all $g$ and all $u$ in the intersection of the level-one subgroup of $N$ with the kernel of $\mathrm{glArch}$ (the level subgroup of the production pins built from $D$, the Hecke generators and the adelic box) and with $x'$ in the archimedean cut submodule of the family $\chi$, the convolution $x'*\beta$ again satisfies both conditions.
--
--   This is the statement that smoothing by the Casimir element at a real place, applied to $\alpha$ through left translations, stays inside the class of admissible factorizable test functions and does not disturb the level structure or the archimedean types of the function being convolved. Together with the identification of the combination $-\big(\tfrac14L_HL_H-\tfrac12L_H+L_EL_{F^-}\big)$ with the Casimir operator `archCasimirAt` on functions smooth at $w$, it feeds the construction of Casimir eigenvalue data on right convolutions of level- and type-constrained functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar.lean

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

theorem AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ :=
      fun y => -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K (ArchTypeFamily.ofChar K χ) β) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' β = fun g => -((1 / 4 : ℂ) * rightConv K x' (L .H (L .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (L .H α) g + rightConv K x' (L .E (L .Fm α)) g)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ)) := by sorry
