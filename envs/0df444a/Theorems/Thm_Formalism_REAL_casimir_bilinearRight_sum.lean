-- Prove2me | Theorems.Thm_Formalism_REAL_casimir_bilinearRight_sum
-- name    : Formalism.REAL.casimir_bilinearRight_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:47.875805+00:00
-- url     : https://prove2.me/theorems/cf9b57dc-6dc7-489c-befb-4edeb4af9414
-- title:
--   REAL: casimir bilinear Right sum
-- statement:
--   The REAL construction uses the casimir bilinear Right sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L220-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L220-L242

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
omit hPP

theorem Formalism.REAL.casimir_bilinearRight_sum :
    ∑ a, ∑ b, bilinearRight B P a b * bilinearRight B P b a = bilinearQuartic B P + n • bilinearNumber B P := by sorry
