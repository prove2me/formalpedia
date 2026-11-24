-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mono_eq_of_counts
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mono_eq_of_counts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:52.374865+00:00
-- url     : https://prove2.me/theorems/8cb9631b-f29c-4e2b-9a1a-f37d160e51b9
-- title:
--   leading Term Lemmas: mono eq of counts
-- statement:
--   The leading Term Lemmas construction uses the mono eq of counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L535-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L535-L552

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n C : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mono_eq_of_counts (f g : Fin C → ℕ) (hf : Monotone f) (hg : Monotone g) (hfn : ∀ c, f c ≤ n)
    (hgn : ∀ c, g c ≤ n)
    (h : ∀ v < n, (univ.filter fun c => f c = v).card = (univ.filter fun c => g c = v).card) : f = g := by sorry
