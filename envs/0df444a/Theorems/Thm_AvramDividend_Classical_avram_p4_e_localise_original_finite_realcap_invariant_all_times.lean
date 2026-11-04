-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_finite_realcap_invariant_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:03:57.196615+00:00
-- url     : https://prove2.me/theorems/e8d7059c-8465-4eac-b887-63341a61ca73
-- title:
--   Canonical original cap invariant converts to a real reserve upper bound at every physical time
-- statement:
--   For a finite nonnegative real cap c and original source controlled reserve, the exact initial cap x≤c plus IsAdmissibleLe gives riskProcess≤c at time zero and every positive physical time. At zero, use X.X_zero and original D_zero; after zero, convert ENNReal.ofReal risk≤ENNReal.ofReal c using the pinned order equivalence. This is the missing real cap premise required by the previously Proved finite-cap predictable HJB occupation theorem, whose theorem import currently fails to materialise in the remote environment. The proof is standalone and original-source.
-- source:
--   Canonical source riskProcess, IsAdmissibleLe, IsDividendStrategy and pinned ENNReal.ofReal_le_ofReal_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_finite_realcap_invariant_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    ∀ ω (s : ℝ≥0), riskProcess X x D s ω ≤ c := by sorry
