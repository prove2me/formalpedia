-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_decomp_of_inv
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.decomp_of_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:50:46.26039+00:00
-- url     : https://prove2.me/theorems/73d91aad-7ac4-5ffa-93ff-dc757df8e86d
-- title:
--   Fr Tan Dir Alg: decomp of inv
-- statement:
--   The Fr Tan Dir Alg construction uses the decomp of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L25-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L25-L86

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.decomp_of_inv (ρ : 𝓞 E →+* Module.End R M) (χ : ι → (𝓞 E →+* R)) (b : Module.Basis κ ℤ (𝓞 E))
    (Cm : κ → ι → R) (hAC : ∀ σ τ, ∑ i, χ σ (b i) * Cm i τ = if σ = τ then 1 else 0)
    (hCA : ∀ i j, ∑ τ, Cm i τ * χ τ (b j) = if i = j then 1 else 0) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by sorry
