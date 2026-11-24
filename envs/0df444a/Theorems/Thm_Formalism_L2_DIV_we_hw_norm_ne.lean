-- Prove2me | Theorems.Thm_Formalism_L2_DIV_we_hw_norm_ne
-- name    : Formalism.L2.DIV.we_hw_norm_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:50.608469+00:00
-- url     : https://prove2.me/theorems/97c63b04-2328-49fe-8ad0-ede33aa3b3e4
-- title:
--   DIV: we hw norm ne
-- statement:
--   The DIV construction uses the we hw norm ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L45-L46

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

theorem Formalism.L2.DIV.we_hw_norm_ne {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : fockQ (hw ℚ hn ν) (hw ℚ hn ν) ≠ 0 := by sorry
