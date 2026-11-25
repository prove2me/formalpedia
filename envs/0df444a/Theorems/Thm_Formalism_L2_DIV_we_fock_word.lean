-- Prove2me | Theorems.Thm_Formalism_L2_DIV_we_fock_word
-- name    : Formalism.L2.DIV.we_fock_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:51.14267+00:00
-- url     : https://prove2.me/theorems/cba52e79-7f6c-4bf1-8317-c50ca055414c
-- title:
--   DIV: we fock word
-- statement:
--   The DIV construction uses the we fock word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean#L61-L66

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

theorem Formalism.L2.DIV.we_fock_word {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ))
    (P : MvPolynomial (Fin r × Fin n) ℚ) (hP : P ∈ dualWeyl ℚ r n ν) :
    fockQ P (applyWord ℚ w (hw ℚ hn ν)) =
      eval (idFrame ℚ r n) (applyWord ℚ (transposeWord w) P) * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by sorry
