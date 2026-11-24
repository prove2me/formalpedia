-- Prove2me | Theorems.Thm_Formalism_L2_DIV_we_span_weyl
-- name    : Formalism.L2.DIV.we_span_weyl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:39.198022+00:00
-- url     : https://prove2.me/theorems/b08e87e6-d1ef-4994-a460-5e61c64c37fa
-- title:
--   DIV: we span weyl
-- statement:
--   The DIV construction uses the we span weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L211-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L211-L219

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
variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

theorem Formalism.L2.DIV.we_span_weyl (hν : Antitone ν) :
    Submodule.span ℚ (((weyl ℤ r n hn ν).map (intQ r n) : Submodule ℤ _) : Set (MvPolynomial (Fin r × Fin n) ℚ)) =
      dualWeyl ℚ r n ν := by sorry
