-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_pow_left
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_pow_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:47.705277+00:00
-- url     : https://prove2.me/theorems/da9c8714-749e-4aba-a67b-062381dece5c
-- title:
--   LL: po pow left
-- statement:
--   The LL construction uses the po pow left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L79-L87

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

theorem Formalism.InvariantFactorPaths.KP.LL.po_pow_left {σ τ : Type} (f : τ → σ) (hf : Function.Injective f) (u : τ)
    (y : MvPolynomial τ ℚ_[p]) {g : MvPolynomial σ ℚ_[p]} (hg : pderiv (f u) g = 0) (k : ℕ) :
    (po_d (f u) ^ k) (rename f y * g) = rename f ((po_d u ^ k) y) * g := by sorry
