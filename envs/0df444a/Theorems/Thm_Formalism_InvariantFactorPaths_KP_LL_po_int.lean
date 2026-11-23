-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_int
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:41.439796+00:00
-- url     : https://prove2.me/theorems/a1025930-0904-49e0-8c3a-d21aaf6b1b38
-- title:
--   LL: po int
-- statement:
--   The LL construction uses the po int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L89-L94

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

theorem Formalism.InvariantFactorPaths.KP.LL.po_int {σ : Type} (v : σ) (k : ℕ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d v ^ k) y) ∈ IntPol p σ := by sorry
