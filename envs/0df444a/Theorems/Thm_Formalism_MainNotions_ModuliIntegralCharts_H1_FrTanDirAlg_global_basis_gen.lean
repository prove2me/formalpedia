-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_global_basis_gen
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.global_basis_gen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:00.578807+00:00
-- url     : https://prove2.me/theorems/7e5e005b-9556-4269-8122-b8e85ea63594
-- title:
--   Fr Tan Dir Alg: global basis gen
-- statement:
--   The Fr Tan Dir Alg construction uses the global basis gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L88-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L88-L122

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.global_basis_gen (ρ : 𝓞 E →+* Module.End R M) (χ : ι → 𝓞 E → R)
    (hdec : (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
      (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0))
    {mult : ι → ℕ} (U : (Σ σ, Fin (mult σ)) → M) (hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = χ σ a • U ⟨σ, i⟩)
    (hb : ∀ σ (W : M), (∀ a : 𝓞 E, ρ a W = χ σ a • W) → ∃! c : Fin (mult σ) → R, ∑ i, c i • U ⟨σ, i⟩ = W)
    (W : M) : ∃! a : (Σ σ, Fin (mult σ)) → R, ∑ ℓ, a ℓ • U ℓ = W := by sorry
