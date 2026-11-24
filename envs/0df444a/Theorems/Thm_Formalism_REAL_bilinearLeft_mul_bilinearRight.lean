-- Prove2me | Theorems.Thm_Formalism_REAL_bilinearLeft_mul_bilinearRight
-- name    : Formalism.REAL.bilinearLeft_mul_bilinearRight
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:12.100275+00:00
-- url     : https://prove2.me/theorems/f7354826-2730-4fa9-bf2d-03bc225fbfa6
-- title:
--   REAL: bilinear Left mul bilinear Right
-- statement:
--   The REAL construction uses the bilinear Left mul bilinear Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L181-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L181-L189

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

theorem Formalism.REAL.bilinearLeft_mul_bilinearRight (i j : Fin m) (a b : Fin n) :
    bilinearLeft B P i j * bilinearRight B P a b = bilinearRight B P a b * bilinearLeft B P i j := by sorry
