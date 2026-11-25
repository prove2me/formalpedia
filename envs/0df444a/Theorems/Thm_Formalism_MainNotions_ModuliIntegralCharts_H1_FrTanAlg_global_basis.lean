-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_global_basis
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.global_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:01.984143+00:00
-- url     : https://prove2.me/theorems/9c57e6c0-ef14-4a0e-9c54-996537d388c7
-- title:
--   Fr Tan Alg: global basis
-- statement:
--   The Fr Tan Alg construction uses the global basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L227-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L227-L260

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.global_basis (χ : ι → (E →+* S)) (hχ : Function.Injective χ)
    (hcard : Fintype.card ι = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End S M) {mult : ι → ℕ}
    (U : (Σ σ, Fin (mult σ)) → M) (hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = χ σ (a : E) • U ⟨σ, i⟩)
    (hb : ∀ σ (W : M), (∀ a : 𝓞 E, ρ a W = χ σ (a : E) • W) →
      ∃! c : Fin (mult σ) → S, ∑ i, c i • U ⟨σ, i⟩ = W)
    (W : M) : ∃! a : (Σ σ, Fin (mult σ)) → S, ∑ ℓ, a ℓ • U ℓ = W := by sorry
