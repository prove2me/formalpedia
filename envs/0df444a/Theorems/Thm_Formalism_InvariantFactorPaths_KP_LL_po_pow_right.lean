-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_pow_right
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_pow_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:37:39.161714+00:00
-- url     : https://prove2.me/theorems/239b370d-c2eb-4501-817e-7f9bbbffadaa
-- title:
--   LL: po pow right
-- statement:
--   The LL construction uses the po pow right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L70-L77

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

theorem Formalism.InvariantFactorPaths.KP.LL.po_pow_right {σ : Type} (v : σ) {a : MvPolynomial σ ℚ_[p]} (ha : pderiv v a = 0)
    (g : MvPolynomial σ ℚ_[p]) (k : ℕ) : (po_d v ^ k) (a * g) = a * (po_d v ^ k) g := by sorry
