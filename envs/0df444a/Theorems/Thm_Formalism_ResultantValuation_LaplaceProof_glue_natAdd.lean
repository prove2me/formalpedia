-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
-- name    : Formalism.ResultantValuation.LaplaceProof.glue_natAdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:41.519792+00:00
-- url     : https://prove2.me/theorems/0da96aad-ade5-4d3f-919a-a1754b15bab6
-- title:
--   Laplace Proof: glue nat Add
-- statement:
--   The Laplace Proof construction uses the glue nat Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L195-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean#L195-L198

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

theorem Formalism.ResultantValuation.LaplaceProof.glue_natAdd (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) (j : Fin b) :
    glue x (Fin.natAdd a j) = (x.1.1ᶜ).orderEmbOfFin (compl_card x.1) (x.2.2 j) := by sorry
