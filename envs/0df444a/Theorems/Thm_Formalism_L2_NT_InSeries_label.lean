-- Prove2me | Theorems.Thm_Formalism_L2_NT_InSeries_label
-- name    : Formalism.L2.NT.InSeries.label
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:13.891941+00:00
-- url     : https://prove2.me/theorems/f5cb9381-33d4-4f24-8276-636dd774f6dd
-- title:
--   In Series: label
-- statement:
--   The In Series construction uses the label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L238-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L238-L265

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {g : ℕ} [Fact g.Prime]

theorem Formalism.L2.NT.InSeries.label {teich : Formalism.CyclotomicNorms.Fbar g →* ℂ} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar g} {r : ℕ}
    {χ : GL (Fin r) (ZMod g) → ℂ} {f : (ZMod g)[X]} (hζ : IsGenSys ζ) (h : InSeries teich ζ χ f) :
    f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0 := by sorry
