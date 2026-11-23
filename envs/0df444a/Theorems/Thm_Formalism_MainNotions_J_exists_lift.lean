-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_exists_lift
-- name    : Formalism.MainNotions.J.exists_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:36.59664+00:00
-- url     : https://prove2.me/theorems/8478b603-a070-4e6e-a56e-b3be59bd9789
-- title:
--   J: exists lift
-- statement:
--   The J construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L340-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L340-L346

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
variable {ι κ : Type} {K : Type} [Field K]

theorem Formalism.MainNotions.J.exists_lift (O : Subring K) (A : MvPowerSeries ι K) (h : ∀ n, coeff n A ∈ O) :
    ∃ A' : MvPowerSeries ι O, map O.subtype A' = A := by sorry
