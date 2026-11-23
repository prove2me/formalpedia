-- Prove2me | Theorems.Thm_Formalism_REAL_CharId_T_apply
-- name    : Formalism.REAL.CharId_T_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:49.117795+00:00
-- url     : https://prove2.me/theorems/0a45f0e9-b6a3-41d4-be2c-3086c95c47fe
-- title:
--   REAL: Char Id T apply
-- statement:
--   The REAL construction uses the Char Id T apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L28-L30

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.CharId_T_apply {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (y : Fin n → V) (x : Fin n) :
    twistedAction E c d y x = E c d (y x) - if x = d then y c else 0 := by sorry
