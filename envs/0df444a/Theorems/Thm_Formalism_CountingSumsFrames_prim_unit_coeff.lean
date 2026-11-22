-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_prim_unit_coeff
-- name    : Formalism.CountingSumsFrames.prim_unit_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:48.141287+00:00
-- url     : https://prove2.me/theorems/a5c90305-5511-42c6-92d1-b3f32f3ae63c
-- title:
--   Counting Sums Frames: prim unit coeff
-- statement:
--   The Counting Sums Frames construction uses the prim unit coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1561-L1592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1561-L1592

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

theorem Formalism.CountingSumsFrames.prim_unit_coeff [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hz : z ∈ YZ p (r := r) LL J M)
    (hprim : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) :
    ∃ m, ‖coeff m z‖ = 1 := by sorry
