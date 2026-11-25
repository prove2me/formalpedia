-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_exists_inv
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.exists_inv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:01.13846+00:00
-- url     : https://prove2.me/theorems/3b2d8acc-99b8-4963-b7fe-63b604bf66bc
-- title:
--   Fr Tan Dir Alg: exists inv
-- statement:
--   The Fr Tan Dir Alg construction uses the exists inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L210-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L210-L269

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
variable (E : Type) [Field E] [NumberField E]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.exists_inv {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by sorry
