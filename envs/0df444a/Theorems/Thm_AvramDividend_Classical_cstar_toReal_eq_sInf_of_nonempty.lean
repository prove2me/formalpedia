-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_toReal_eq_sInf_of_nonempty
-- name    : AvramDividend.Classical.cstar_toReal_eq_sInf_of_nonempty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:21:21.15498+00:00
-- url     : https://prove2.me/theorems/22482435-2395-45af-98ab-241b7a4cf26d
-- title:
--   Canonical Avram barrier equals the real infimum of the positive derivative-minimiser set
-- statement:
--   If the set of positive global minimisers of the derivative W' is nonempty, the real value of the canonical Avram barrier cstar W, defined as the ENNReal infimum of the real minimisers, equals the ordinary real infimum of that set. All members are positive, so the infimum is finite. This is the exact coercion/infimum bridge required to combine continuous_argmin_sInf_zero_or_minimal with cstar_finite_zero_or_deriv_minimal.
-- source:
--   Formal definitions cstarSet and cstar in Definitions.Def_AvramDividend_Classical_ScaleFunction; pinned Mathlib ENNReal.toReal_iInf, iInf_subtype, and real infimum of subtype. This is the representation step for Avram Palmowski Pistorius, Proposition 3(i) and Lemma 2(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cstar_toReal_eq_sInf_of_nonempty
    (W : ℝ → ℝ) (hS : (cstarSet W).Nonempty) :
    (cstar W).toReal = sInf (cstarSet W) := by sorry
