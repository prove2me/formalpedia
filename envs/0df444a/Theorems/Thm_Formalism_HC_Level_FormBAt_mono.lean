-- Prove2me | Theorems.Thm_Formalism_HC_Level_FormBAt_mono
-- name    : Formalism.HC.Level.FormBAt.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:24.921949+00:00
-- url     : https://prove2.me/theorems/ea542feb-4c64-41e4-ae05-98d24dfbe337
-- title:
--   Form BAt: mono
-- statement:
--   The Form BAt construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean#L37-L44

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Window
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.HC.Level
variable (Λ : Level)
variable {Λ}

theorem Formalism.HC.Level.FormBAt.mono {la la' : ℝ} (h : Λ.FormBAt la) (hl : la ≤ la') : Λ.FormBAt la' := by sorry
