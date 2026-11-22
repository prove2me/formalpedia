-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
-- name    : Formalism.ResultantValuation.LaplaceProof.glue_castAdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:53.528605+00:00
-- url     : https://prove2.me/theorems/ad67ac62-21cd-4ea0-9305-e98fe43d25f0
-- title:
--   Laplace Proof: glue cast Add
-- statement:
--   The Laplace Proof construction uses the glue cast Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L190-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L190-L193

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}

theorem Formalism.ResultantValuation.LaplaceProof.glue_castAdd (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) (i : Fin a) :
    glue x (Fin.castAdd b i) = x.1.1.orderEmbOfFin x.1.2 (x.2.1 i) := by sorry
