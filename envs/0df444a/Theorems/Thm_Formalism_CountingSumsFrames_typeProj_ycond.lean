-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_typeProj_ycond
-- name    : Formalism.CountingSumsFrames.typeProj_ycond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:21.442158+00:00
-- url     : https://prove2.me/theorems/41d7145b-fae2-4973-aa25-edd67c9c01a3
-- title:
--   Counting Sums Frames: type Proj ycond
-- statement:
--   The Counting Sums Frames construction uses the type Proj ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1201-L1205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1201-L1205

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.typeProj_ycond [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (Mt : WithTop ℤ) :
    ∀ x ∈ YCond p (r := r) LL j Mt, P x ∈ YCond p (r := r) LL j Mt := by sorry
