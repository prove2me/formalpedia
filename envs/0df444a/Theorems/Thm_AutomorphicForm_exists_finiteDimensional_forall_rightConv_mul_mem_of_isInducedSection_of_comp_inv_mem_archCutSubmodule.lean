-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b6e5c0c6-348a-5e79-8094-37f4b119f017
-- title:
--   Uniform finite-dimensional K_w-type for right convolutions of induced sections
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}=$ `AdeleRing (𝓞 F) F` and $G=\mathrm{GL}_2(\mathbb{A})$, let $\eta\colon \mathbb{A}^\times\to\mathbb{C}^\times$ be a character (a monoid homomorphism), let $f\colon G\to\mathbb{C}$ be continuous with compact support, let `tys` be an `ArchTypeFamily F`, i.e. a number $\mathrm{card}\,v$ for each infinite place $v$ together with representations $\mathrm{rep}\,v\,i$ ($i<\mathrm{card}\,v$) of the row-isometry group `rowIsometrySubgroup₀ v.Completion` on finite-dimensional spaces $\mathbb{C}^n$, and assume $x\mapsto f(x^{-1})$ lies in `archCutSubmodule F tys`, the intersection over all infinite places $v$ of the sums over $i$ of the submodules `archTypeSubmoduleAt F v (tys.rep v i)` attached to those representations along `rowIsometryInclAt₀ F v`. Fix an infinite place $w$ and let $K_w\le G$ be `archRowIsometrySubgroup F w`, the image under `adelicArchGLInclAt F w` of the subgroup of $\mathrm{GL}_2(F_w)$ of row isometries. Then there is a single $\mathbb{C}$-submodule $W$ of the functions $K_w\to\mathbb{C}$, finite-dimensional over $\mathbb{C}$, with the following property: for every pair of characters $\chi_1,\chi_2$ of $\mathbb{A}^\times$ with $\chi_1(x)\chi_2(x)=\eta(x)$ for all $x$, every continuous $\varphi\colon G\to\mathbb{C}$ satisfying `IsInducedSection`, i.e. $\varphi(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi(g)$ for all $g\in G$ and all $b$ in the adelic Borel subgroup (those $b$ with $b_{10}=0$), and every $g\in G$, the function $k\mapsto (\mathrm{rightConv}\,F\,\varphi\,f)(gk)=\int_G \varphi(gkx)f(x)\,dx$, the integral being against the Haar measure `adelicGLHaar` on $G$, belongs to $W$. In particular $W$ depends only on $F$, $\eta$, $f$, `tys` and $w$, not on $(\chi_1,\chi_2)$, $\varphi$ or $g$.
--
--   This is the uniform $K_w$-finiteness statement: right convolution of any principal-series-type induced section by a fixed archimedean-bi-finite test function lands, after arbitrary left translation, in one and the same finite-dimensional space of functions on the compact group $K_w$, uniformly over all inducing pairs with fixed product character $\eta$. It supplies the 'one $K_w$-type for all inducing parameters' clause used in [`AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite`](thm.html#AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite), where Paley–Wiener families $\chi_1=\mu|\cdot|^{s+1/2}$, $\chi_2=\nu|\cdot|^{-(s+1/2)}$ all have $\chi_1\chi_2=\mu\nu$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (tys : ArchTypeFamily F) (_hfty : (fun x => f x⁻¹) ∈ archCutSubmodule F tys)
    (w : InfinitePlace F) :
    ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ), FiniteDimensional ℂ W ∧
      ∀ (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), (∀ x, χ₁ x * χ₂ x = η x) →
      ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ), IsInducedSection (𝓞 F) F χ₁ χ₂ φ → Continuous φ →
      ∀ g : AdelicGL2 (𝓞 F) F,
        (fun k : ↥(archRowIsometrySubgroup F w) => rightConv F φ f (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W := by sorry
