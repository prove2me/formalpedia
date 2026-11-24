-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_R_step
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_R_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:40.469795+00:00
-- url     : https://prove2.me/theorems/88544649-dbc2-496a-8a6a-738185e81f70
-- title:
--   LL: po R step
-- statement:
--   The LL construction uses the po R step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L116-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L116-L133

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
variable {N r : ℕ} [NeZero r] {D : BlockData N}
omit [NeZero r]

theorem Formalism.InvariantFactorPaths.KP.LL.po_R_step {t b : ℕ} (c : Fin r) {g : MvPolynomial (BVar N r t) ℚ_[p]} (hg : g ∈ po_R p N r t b) :
    pderiv (xiVar N r t c) g ∈ po_R p N r t (b - 1) := by sorry
