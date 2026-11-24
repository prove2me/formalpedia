-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_typeProj_eul
-- name    : Formalism.CountingSumsFrames.typeProj_eul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:30.788798+00:00
-- url     : https://prove2.me/theorems/a43a9277-b9b9-4ed7-ab64-8566a3967e71
-- title:
--   Counting Sums Frames: type Proj eul
-- statement:
--   The Counting Sums Frames construction uses the type Proj eul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1170-L1175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1170-L1175

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

theorem Formalism.CountingSumsFrames.typeProj_eul (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (i0 : Fin N) :
    ∀ x, P (ProjS.eulL (fun c : Fin r => (i0, c)) x) = ProjS.eulL (fun c : Fin r => (i0, c)) (P x) := by sorry
