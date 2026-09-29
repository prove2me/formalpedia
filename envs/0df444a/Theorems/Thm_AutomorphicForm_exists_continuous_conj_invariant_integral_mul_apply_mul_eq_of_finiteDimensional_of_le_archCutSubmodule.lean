-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
-- name    : AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/2ab2b747-4ce8-5d3c-a2b5-bdc48fac975e
-- title:
--   Continuous central idempotent reproducing a finite-dimensional archimedean type space
-- statement:
--   Let $F$ be a number field and write $\mathcal{K} = \prod_{w \mid \infty} \mathrm{rowIsometrySubgroup}_0(F_w)$ for the product over the infinite places of the norm-one row-isometry subgroups of $\mathrm{GL}_2(F_w)$, equipped with a measurable structure which is the Borel structure of its topology. Let $\mu$ be a probability measure on $\mathcal{K}$ invariant under both left and right translation, and let $\iota : \mathcal{K} \to \mathrm{GL}_2(F_\infty)$ be a group homomorphism whose $w$-component, obtained by applying evaluation at $w$ entrywise, is $\kappa \mapsto \kappa_w$ for every $w$. Let `tys` be an archimedean type family, that is, a cardinality function $w \mapsto \mathrm{card}(w)$ together with, for each $w$ and each $i \in \mathrm{Fin}(\mathrm{card}(w))$, a representation $\rho_{w,i}$ of $\mathrm{rowIsometrySubgroup}_0(F_w)$ on some $\mathbb{C}^{n}$. Let $E$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ which is finite-dimensional over $\mathbb{C}$, consists of continuous functions, is contained in the archimedean cut $\bigsqcap_w \bigsqcup_i \mathrm{typeSubmodule}$ of `tys` (for each $w$, the join over $i$ of the spans of the ranges of the $\mathbb{C}$-linear maps $T$ into functions on $\mathrm{GL}_2(\mathbb{A}_F)$ satisfying $T(\rho_{w,i}(k)v)(x) = (Tv)(x \cdot k_w)$), and is stable under the right translations $v \mapsto v(\,\cdot\, \bar\iota(\kappa))$, where $\bar\iota(\kappa)$ denotes $\iota(\kappa)$ placed in the archimedean factor and $1$ in the finite factor. Then there is a continuous $e : \mathcal{K} \to \mathbb{C}$ which is invariant under conjugation, satisfies $e(\kappa^{-1}) = \overline{e(\kappa)}$, lies for each $w$ in the join over $i$ of the type submodules of functions on $\mathcal{K}$ attached to the contragredients $\rho_{w,i}^{\vee}$ along the homomorphism placing an element of $\mathrm{rowIsometrySubgroup}_0(F_w)$ at $w$ and $1$ elsewhere, is such that $\kappa \mapsto e(\kappa^{-1})$ lies in the corresponding join for the $\rho_{w,i}$ themselves, and reproduces $E$: for all $v \in E$ and all $x \in \mathrm{GL}_2(\mathbb{A}_F)$, $\int_{\mathcal{K}} e(\kappa)\, v(x \cdot \bar\iota(\kappa))\, d\mu(\kappa) = v(x)$.
--
--   This produces the elementary idempotent (type projector) attached to the archimedean types occurring in a finite-dimensional, right $\mathcal{K}$-stable space of continuous automorphic functions: convolution against $e$ acts as the identity on that space. It is used in the approximation arguments for the cuspidal spectrum, where elements of a cusp space must be replaced by functions of prescribed archimedean type without changing them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule.lean

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

theorem AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
    (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hE : FiniteDimensional ℂ ↥E)
    (hEc : ∀ v ∈ E, Continuous v) (hEt : E ≤ archCutSubmodule F tys)
    (hEK : ∀ v ∈ E, ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), (fun x => v (x * adelicArchGLIncl F (ι κ))) ∈ E) :
    ∃ e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ,
      Continuous e ∧
      (∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ' * κ * κ'⁻¹) = e κ) ∧
      (∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ)) ∧
      (∀ w : InfinitePlace F,
        e ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ.dual) ∧
      (∀ w : InfinitePlace F,
        (fun κ => e κ⁻¹) ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ) ∧
      ∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 F) F,
        ∫ κ, e κ * v (x * adelicArchGLIncl F (ι κ)) ∂μ = v x := by sorry
