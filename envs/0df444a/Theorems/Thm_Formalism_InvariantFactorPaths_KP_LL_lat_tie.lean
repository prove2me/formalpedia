-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_lat_tie
-- name    : Formalism.InvariantFactorPaths.KP.LL.lat_tie
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:35.549804+00:00
-- url     : https://prove2.me/theorems/623a16a3-59cf-4683-9e32-17f24cc238ce
-- title:
--   LL: lat tie
-- statement:
--   The LL construction uses the lat tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeEqualHolds.lean#L96-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeEqualHolds.lean#L96-L109

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

theorem Formalism.InvariantFactorPaths.KP.LL.lat_tie (hB : D.BlockOK) (hF : HypJoin p (r := r) D) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t)
    (m L : ℕ) (hmL : Nat.log p m ≤ L) :
    ∀ x ∈ Lat p D (r := r) j jp, (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) •
      (tieF (wv D i) (ev D i) ^ m) x) ∈ Lat p D (r := r) (j + Pi.single i m) jp := by sorry
