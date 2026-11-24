-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_letters_zero
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.letters_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:39.711209+00:00
-- url     : https://prove2.me/theorems/440b5a54-0017-48b0-bfaa-bdf5b7972849
-- title:
--   Free Action Expansion: letters zero
-- statement:
--   The Free Action Expansion construction uses the letters zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L98-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L98-L107

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S V : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S] [AddCommGroup V]
  [Module A V]

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.letters_zero (P Q : A[X]) (a : S) (x : Ix S → V) (hx : ∀ u, u a ≠ 0 → x u = 0) :
    ∀ L : List (Letter ℂ S), a ∉ L.map Letter.intersection_update_fsHerm_neg_one → ∀ u, u a ≠ 0 → letters P Q L x u = 0 := by sorry
