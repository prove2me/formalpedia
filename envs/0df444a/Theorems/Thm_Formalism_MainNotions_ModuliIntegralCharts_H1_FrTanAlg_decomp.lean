-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_decomp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.decomp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:03.573837+00:00
-- url     : https://prove2.me/theorems/3939f0ee-920b-4352-aec4-211a10cf7ec4
-- title:
--   Fr Tan Alg: decomp
-- statement:
--   The Fr Tan Alg construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L166-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L166-L225

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable {E : Type} [Field E] [NumberField E] {S M : Type} [Field S] [CharZero S] [AddCommGroup M] [Module S M]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.decomp (χ : ι → (E →+* S)) (hχ : Function.Injective χ) (hcard : Fintype.card ι = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End S M) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ (a : E) • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ (a : E) • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by sorry
