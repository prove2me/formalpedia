-- Prove2me | Theorems.Thm_Formalism_L2_DIV_we_eval_idFrame_map
-- name    : Formalism.L2.DIV.we_eval_idFrame_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:04.487797+00:00
-- url     : https://prove2.me/theorems/80476eb7-f721-40d3-aee1-bc9ea79ec9ec
-- title:
--   DIV: we eval id Frame map
-- statement:
--   The DIV construction uses the we eval id Frame map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L48-L55

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility

theorem Formalism.L2.DIV.we_eval_idFrame_map {r n : ℕ} (G : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (MvPolynomial.map (Int.castRingHom ℚ) G) = ((eval (idFrame ℤ r n) G : ℤ) : ℚ) := by sorry
