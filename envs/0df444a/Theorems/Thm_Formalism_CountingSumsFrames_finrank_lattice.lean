-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_finrank_lattice
-- name    : Formalism.CountingSumsFrames.finrank_lattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:29.197789+00:00
-- url     : https://prove2.me/theorems/9a337126-f14b-4944-b123-2f109ba99fb2
-- title:
--   Counting Sums Frames: finrank lattice
-- statement:
--   The Counting Sums Frames construction uses the finrank lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L127-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L127-L148

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
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.finrank_lattice {N r : ℕ} (LL : Letters N) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : S ≤ Pol p r LL) :
    Module.finrank ℤ_[p] (S.restrictScalars ℤ_[p] ⊓ PolZ p r LL : Submodule ℤ_[p] _) = Module.finrank ℚ_[p] S := by sorry
