-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_coord
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:43.425738+00:00
-- url     : https://prove2.me/theorems/d4473cb3-11aa-4f2e-a8d6-16f2fdef8033
-- title:
--   LL: po coord
-- statement:
--   The LL construction uses the po coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L163-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L163-L184

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

theorem Formalism.InvariantFactorPaths.KP.LL.po_coord (hU : HypU p (r := r) D) (j : Fin D.T.t → ℕ) (c : Fin r) (k jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k) x) ∈ Lat p D (r := r) j (jp + k) := by sorry
