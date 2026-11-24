-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_xi_div
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_xi_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:37:03.449014+00:00
-- url     : https://prove2.me/theorems/44e7f825-91fb-45ca-8840-cff7432046fa
-- title:
--   LL: po xi div
-- statement:
--   The LL construction uses the po xi div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L146-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L146-L150

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

theorem Formalism.InvariantFactorPaths.KP.LL.po_xi_div {t b : ℕ} (c : Fin r) (k : ℕ) {g : MvPolynomial (BVar N r t) ℚ_[p]}
    (hg : g ∈ XiPolZ p N r t b) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d (xiVar N r t c) ^ k) g) ∈ XiPolZ p N r t (b - k) := by sorry
