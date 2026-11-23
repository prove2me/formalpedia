-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_coeff_Ex
-- name    : Formalism.MainNotions.J.coeff_Ex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:08.148576+00:00
-- url     : https://prove2.me/theorems/bc70a945-7e40-485d-9408-0f6e3eaeb995
-- title:
--   J: coeff Ex
-- statement:
--   The J construction uses the coeff Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L330-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L330-L332

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
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
open MvPowerSeries
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']

theorem Formalism.MainNotions.J.coeff_Ex {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) (n : ι →₀ ℕ) :
    coeff n (Ex f) = ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ * coeff n (f ^ k) := by sorry
