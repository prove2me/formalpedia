-- Prove2me | Theorems.Thm_Formalism_REAL_CharId_F_gen
-- name    : Formalism.REAL.CharId_F_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:28.194901+00:00
-- url     : https://prove2.me/theorems/d7f143f1-953f-4839-947f-36db15cbe1bb
-- title:
--   REAL: Char Id F gen
-- statement:
--   The REAL construction uses the Char Id F gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L78-L80

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

theorem Formalism.REAL.CharId_F_gen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (j : ℕ) (t : Fin n) (ht : j ≤ (t : ℕ)) :
    Pi.single t v ∈ CharId_F E v j := by sorry
