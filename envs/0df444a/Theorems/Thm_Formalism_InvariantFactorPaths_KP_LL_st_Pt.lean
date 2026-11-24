-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_Pt
-- name    : Formalism.InvariantFactorPaths.KP.LL.st_Pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:37:13.373599+00:00
-- url     : https://prove2.me/theorems/d6e20149-04d0-4f55-a978-7ddae295475e
-- title:
--   LL: st Pt
-- statement:
--   The LL construction uses the st Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L51-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L51-L101

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {D}

theorem Formalism.InvariantFactorPaths.KP.LL.st_Pt (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (kk : Fin D.T.t)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    Pt p D j jp kk y = tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk)
      (D.LL.deg (D.letterAt (D.T.pos kk)) - j kk) (D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk) (D.T.z kk) y := by sorry
