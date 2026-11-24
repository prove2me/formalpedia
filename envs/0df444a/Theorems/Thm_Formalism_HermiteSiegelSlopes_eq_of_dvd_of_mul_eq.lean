-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_eq_of_dvd_of_mul_eq
-- name    : Formalism.HermiteSiegelSlopes.eq_of_dvd_of_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:13.245142+00:00
-- url     : https://prove2.me/theorems/4f4b17ac-d629-4419-913d-bb5c6fdc11bb
-- title:
--   Hermite Siegel Slopes: eq of dvd of mul eq
-- statement:
--   The Hermite Siegel Slopes construction uses the eq of dvd of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L538-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L538-L550

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain

theorem Formalism.HermiteSiegelSlopes.eq_of_dvd_of_mul_eq {a1 a2 b1 b2 : ℕ} (h1 : b1 ∣ a1) (h2 : b2 ∣ a2) (h : b1 * b2 = a1 * a2)
    (h0 : a1 * a2 ≠ 0) : b1 = a1 := by sorry
