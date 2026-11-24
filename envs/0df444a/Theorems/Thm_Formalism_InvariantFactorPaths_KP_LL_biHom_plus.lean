-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_biHom_plus
-- name    : Formalism.InvariantFactorPaths.KP.LL.biHom_plus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:52.371802+00:00
-- url     : https://prove2.me/theorems/2e290887-74ab-44d3-b65e-f38cc1eeac21
-- title:
--   LL: bi Hom plus
-- statement:
--   The LL construction uses the bi Hom plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L93-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L93-L117

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus
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

theorem Formalism.InvariantFactorPaths.KP.LL.biHom_plus (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wU D) (xiVar N r D.T.t) ((D.lettersAt j jp).deg D.uPos) (D.B - jp) x := by sorry
