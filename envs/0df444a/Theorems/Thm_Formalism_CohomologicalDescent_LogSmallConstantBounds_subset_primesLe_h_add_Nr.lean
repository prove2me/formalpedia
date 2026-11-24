-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_subset_primesLe_h_add_Nr
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.subset_primesLe_h_add_Nr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:57.190146+00:00
-- url     : https://prove2.me/theorems/288d57e7-a074-4a8d-a76a-3fdaf08faf88
-- title:
--   Log Small Constant Bounds: subset primes Le h add Nr
-- statement:
--   The Log Small Constant Bounds construction uses the subset primes Le h add Nr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L851-L856
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L851-L856

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.subset_primesLe_h_add_Nr {P : Par} (H : P.Hyp) (G : P.Large) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) : R ⊆ pr (P.h + (P.Nr : ℝ)) := by sorry
