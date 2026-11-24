-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_adj_applyWord_cons
-- name    : Formalism.L2.G.Model.TS.adj_applyWord_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:47.065724+00:00
-- url     : https://prove2.me/theorems/c1a0452a-3c18-4f20-8b8d-70c5da13534e
-- title:
--   TS: adj apply Word cons
-- statement:
--   The TS construction uses the adj apply Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingDividedAdjoint.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingDividedAdjoint.lean#L97-L100

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility

theorem Formalism.L2.G.Model.TS.adj_applyWord_cons {R : Type*} [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) F = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w F) := by sorry
