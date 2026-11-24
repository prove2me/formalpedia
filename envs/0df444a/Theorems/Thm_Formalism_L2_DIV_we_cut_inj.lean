-- Prove2me | Theorems.Thm_Formalism_L2_DIV_we_cut_inj
-- name    : Formalism.L2.DIV.we_cut_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:50.99754+00:00
-- url     : https://prove2.me/theorems/59d2e52a-061a-4ee2-ac7f-3ca9b57b1097
-- title:
--   DIV: we cut inj
-- statement:
--   The DIV construction uses the we cut inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L162-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L162-L173

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

theorem Formalism.L2.DIV.we_cut_inj {S S' : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)} (hS : ∀ x ∈ S, x ∈ dualWeyl ℚ r n ν)
    (hS' : ∀ x ∈ S', x ∈ dualWeyl ℚ r n ν) (h : weCut r n ν S = weCut r n ν S') : S = S' := by sorry
