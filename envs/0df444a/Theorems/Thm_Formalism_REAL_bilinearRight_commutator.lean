-- Prove2me | Theorems.Thm_Formalism_REAL_bilinearRight_commutator
-- name    : Formalism.REAL.bilinearRight_commutator
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:10.131795+00:00
-- url     : https://prove2.me/theorems/9a09b092-c8b5-4ad3-a7ac-7d221196393b
-- title:
--   REAL: bilinear Right commutator
-- statement:
--   The REAL construction uses the bilinear Right commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L170-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L170-L179

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {A : Type*} [Ring A] {m n : ℕ} (B P : Fin m → Fin n → A)
variable {B P}
variable (hBP : ∀ i j a b, B i a * P j b - P j b * B i a = if i = j ∧ a = b then 1 else 0)
  (hBB : ∀ i j a b, B i a * B j b = B j b * B i a)
  (hPP : ∀ i j a b, P i a * P j b = P j b * P i a)
include hBP hBB hPP

theorem Formalism.REAL.bilinearRight_commutator (a b c d : Fin n) :
    bilinearRight B P a b * bilinearRight B P c d - bilinearRight B P c d * bilinearRight B P a b =
      (if a = d then bilinearRight B P c b else 0) - (if c = b then bilinearRight B P a d else 0) := by sorry
