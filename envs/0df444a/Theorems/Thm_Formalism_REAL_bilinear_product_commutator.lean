-- Prove2me | Theorems.Thm_Formalism_REAL_bilinear_product_commutator
-- name    : Formalism.REAL.bilinear_product_commutator
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:07.582727+00:00
-- url     : https://prove2.me/theorems/33ccaba0-d2ba-4080-8100-c74b46bf3b35
-- title:
--   REAL: bilinear product commutator
-- statement:
--   The REAL construction uses the bilinear product commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L147-L152

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

theorem Formalism.REAL.bilinear_product_commutator (i j k l : Fin m) (a b c d : Fin n) :
    P i a * B j b * (P k c * B l d) - P k c * B l d * (P i a * B j b) =
      (if j = k ∧ b = c then 1 else 0) * (P i a * B l d) -
        (if l = i ∧ d = a then 1 else 0) * (P k c * B j b) := by sorry
