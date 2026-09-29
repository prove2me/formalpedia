-- Prove2me | Theorems.Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
-- name    : AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/a24059a0-d842-5722-8a01-0a44f24b22cd
-- title:
--   Two-sided K-averages of archimedean test factors
-- statement:
--   Let $F$ be a number field, and write $\mathcal{K} = \prod_{w \mid \infty}$ `rowIsometrySubgroup₀ w.Completion` for the product, over the infinite places of $F$, of the groups `rowIsometrySubgroup₀ w.Completion`, equipped with a Borel measurable structure. Let $\mu$ be a finite measure on $\mathcal{K}$ that is invariant under both left and right translation, and let $\iota \colon \mathcal{K} \to GL_2(F_\infty)$ be a group homomorphism into $GL_2$ of the infinite adele ring such that for every $\kappa \in \mathcal{K}$ and every infinite place $w$ the image of $\iota(\kappa)$ under the componentwise map `archComponent F w` to $GL_2(F_w)$ is the image of $\kappa_w$; thus $\iota$ places the $w$-component at $w$. Let `tys` be an archimedean type family for $F$, that is, a number `tys.card w` for each infinite place $w$ together with data `tys.rep w i` ($i <$ `tys.card w`), each consisting of an $n$ and a representation $\rho$ of `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$. Let $e_1, e_2 \colon \mathcal{K} \to \mathbb{C}$ be continuous, and let $h \colon GL_2(F_\infty) \to \mathbb{C}$ be an archimedean test factor, i.e. $h$ has compact support and factors as $h(g) = \Phi(\mathrm{archEntries}(g))$ for some $\Phi$ on the $2 \times 2$ matrices over the mixed space of $F$ that is $C^\infty$ over $\mathbb{R}$, where `archEntries` transports the entries of $g$ to the mixed space. Set $$\varphi(y) = \int_{\mathcal{K} \times \mathcal{K}} e_1(\kappa_1)\, e_2(\kappa_2)\, h\big(\iota(\kappa_1)^{-1} y\, \iota(\kappa_2)^{-1}\big)\, d(\mu \otimes \mu).$$ The conclusion is twofold. First, $\varphi$ is again an archimedean test factor in the above sense. Second, assume that for every infinite place $w$ the function $e_2$ lies in the supremum, over $i <$ `tys.card w`, of the submodules `typeSubmodule` attached to the inclusion `MonoidHom.mulSingle` of the $w$-th factor into $\mathcal{K}$ and to the dual of `(tys.rep w i).ρ` — each such submodule being the span of the functions in the range of some linear map $T$ from the representation space to functions on $\mathcal{K}$ satisfying $T(\rho(k)v)(x) = T(v)(x\,\iota(k))$ — and that, likewise for every $w$, the function $\kappa \mapsto e_1(\kappa^{-1})$ lies in the corresponding supremum formed with `(tys.rep w i).ρ` itself. Then $\varphi$ is bi-finite of type `tys`: the function $y \mapsto \varphi(y^{-1})$ lies in $\bigsqcap_w \bigsqcup_i$ `archFactorTypeSubmoduleAt F w (tys.rep w i)` and $\varphi$ lies in $\bigsqcap_w \bigsqcup_i$ `archFactorDualTypeSubmoduleAt F w (tys.rep w i)`.
--
--   This is the smoothing construction that produces bi-isotypic elements of the archimedean Hecke algebra of $GL_2(F_\infty)$ by averaging a test function on both sides against continuous weights on the maximal compact $\mathcal{K}$, with the types of the weights prescribing the types of the average. It is used in the approximation arguments for the cuspidal spectrum, which construct test functions of prescribed level and archimedean type close to a given element of the cuspidal carrier.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
    (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (e₁ e₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hh : IsArchTestFactor F h) :
    IsArchTestFactor F (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        e₁ p.1 * e₂ p.2 * h ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ)) ∧
    ((∀ w : InfinitePlace F,
        e₂ ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ.dual) →
      (∀ w : InfinitePlace F,
        (fun κ => e₁ κ⁻¹) ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ) →
      IsArchFactorBiFinite F tys (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        e₁ p.1 * e₂ p.2 * h ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ))) := by sorry
