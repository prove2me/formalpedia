-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem
-- name    : AutomorphicForm.exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/01e9172c-aeae-58ca-80d0-54cfa355b121
-- title:
--   Self-adjoint convolution unit for a finite-dimensional translation-stable subspace
-- statement:
--   Let $K_c$ be a group carrying a topology making it a compact Hausdorff second countable topological group, equipped with its Borel $\sigma$-algebra, and let $\mu$ be a probability measure on $K_c$ that is both left and right multiplication invariant and positive on nonempty open sets. Let $E$ be a finite-dimensional $\mathbb{C}$-subspace of the space of all functions $K_c \to \mathbb{C}$ such that: every $v \in E$ is continuous; for every $k \in K_c$ and $v \in E$ the right translate $x \mapsto v(xk)$ lies in $E$; for every $k$ and $v \in E$ the left translate $x \mapsto v(kx)$ lies in $E$; and for every $v \in E$ the function $x \mapsto \overline{v(x^{-1})}$ lies in $E$. The assertion is that there exists a function $e : K_c \to \mathbb{C}$ which is continuous, whose inversion $k \mapsto e(k^{-1})$ belongs to $E$, which satisfies $e(k^{-1}) = \overline{e(k)}$ for all $k$, is a convolution idempotent in the sense that $\int_{K_c} e(k')\,e(k'^{-1}k)\,d\mu(k') = e(k)$ for all $k \in K_c$, and acts as the identity by right averaging: $\int_{K_c} e(k)\,v(xk)\,d\mu(k) = v(x)$ for all $v \in E$ and all $x \in K_c$.
--
--   The hypotheses say that $E$ is a finite-dimensional two-sided, involution-stable ideal of the convolution algebra of continuous functions on the compact group $K_c$, and the conclusion produces its self-adjoint unit. It is used to manufacture continuous idempotent kernels on maximal compact subgroups in the adelic theory of automorphic forms, where such a kernel cuts out a prescribed finite-dimensional space of $K$-types.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem
    {Kc : Type*} [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [T2Space Kc]
    [SecondCountableTopology Kc] [MeasurableSpace Kc] [BorelSpace Kc]
    (μ : Measure Kc) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure]
    (E : Submodule ℂ (Kc → ℂ)) [FiniteDimensional ℂ E]
    (hEc : ∀ v ∈ E, Continuous v)
    (hEr : ∀ k : Kc, ∀ v ∈ E, (fun x => v (x * k)) ∈ E)
    (hEl : ∀ k : Kc, ∀ v ∈ E, (fun x => v (k * x)) ∈ E)
    (hEs : ∀ v ∈ E, (fun x => conj (v x⁻¹)) ∈ E) :
    ∃ e : Kc → ℂ, Continuous e ∧ (fun k => e k⁻¹) ∈ E ∧
      (∀ k : Kc, e k⁻¹ = conj (e k)) ∧
      (∀ k : Kc, ∫ k', e k' * e (k'⁻¹ * k) ∂μ = e k) ∧
      (∀ v ∈ E, ∀ x : Kc, ∫ k, e k * v (x * k) ∂μ = v x) := by sorry
