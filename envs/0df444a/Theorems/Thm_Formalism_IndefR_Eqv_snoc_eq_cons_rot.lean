-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_snoc_eq_cons_rot
-- name    : Formalism.IndefR.Eqv.snoc_eq_cons_rot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:08.959649+00:00
-- url     : https://prove2.me/theorems/2544f9c2-d5e9-415f-8adc-f4c6748a5058
-- title:
--   Eqv: snoc eq cons rot
-- statement:
--   The Eqv construction uses the snoc eq cons rot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean#L37-L43

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem Formalism.IndefR.Eqv.snoc_eq_cons_rot {n : ℕ} (w : V) (vs : Fin n → V) :
    (Fin.snoc vs w : Fin (n + 1) → V) = (Fin.cons w vs : Fin (n + 1) → V) ∘ finRotate (n + 1) := by sorry
