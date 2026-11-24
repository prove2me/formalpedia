-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_splits_sub
-- name    : Formalism.MainNotions.J.splits_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:37.479516+00:00
-- url     : https://prove2.me/theorems/e90dc235-2181-4ba7-8267-d076adc268bb
-- title:
--   J: splits sub
-- statement:
--   The J construction uses the splits sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L129-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L129-L149

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem Formalism.MainNotions.J.splits_sub (hp : p.Prime)
    (h : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L) :
    Nat.card {v : HeightOneSpectrum (𝓞 K) // ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} = Module.finrank ℚ K ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → Nat.card (𝓞 K ⧸ v.asIdeal) = p := by sorry
