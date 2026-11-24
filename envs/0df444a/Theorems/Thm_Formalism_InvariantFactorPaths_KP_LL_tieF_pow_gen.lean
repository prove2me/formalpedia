-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieF_pow_gen
-- name    : Formalism.InvariantFactorPaths.KP.LL.tieF_pow_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:43.4922+00:00
-- url     : https://prove2.me/theorems/c5374956-8632-4121-b254-1b5dc25bfd6c
-- title:
--   LL: tie F pow gen
-- statement:
--   The LL construction uses the tie F pow gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeEqualHolds.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeEqualHolds.lean#L58-L67

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
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

theorem Formalism.InvariantFactorPaths.KP.LL.tieF_pow_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) (m : ℕ) :
    (tieF (wv D i) (ev D i) ^ m) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        ((tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y) * g := by sorry
