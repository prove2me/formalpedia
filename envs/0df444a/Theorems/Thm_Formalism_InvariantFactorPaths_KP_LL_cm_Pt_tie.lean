-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_Pt_tie
-- name    : Formalism.InvariantFactorPaths.KP.LL.cm_Pt_tie
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:17.0558+00:00
-- url     : https://prove2.me/theorems/8ce571ab-6379-499f-bbc1-0f5d09defb5f
-- title:
--   LL: cm Pt tie
-- statement:
--   The LL construction uses the cm Pt tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L127-L132

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem Formalism.InvariantFactorPaths.KP.LL.cm_Pt_tie (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp m : ℕ) {i k : Fin D.T.t} (h : i ≠ k)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (tieF (wv D k) (ev D k) ^ m) (Pt p D j jp i x) = Pt p D j jp i ((tieF (wv D k) (ev D k) ^ m) x) := by sorry
