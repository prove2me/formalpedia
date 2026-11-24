-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_AdmissibleUnits_conj_ne
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.conj_ne
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:08.66741+00:00
-- url     : https://prove2.me/theorems/e63c335e-bdaf-44a7-92a5-143813c3014b
-- title:
--   Admissible Units: conj ne
-- statement:
--   The Admissible Units construction uses the conj ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/UnitsEqOneOrNegOne.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/UnitsEqOneOrNegOne.lean#L52-L60

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_UnitsEqOneOrNegOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.conj_ne (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (φ : K →+* ℂ) :
    starRingEnd ℂ (φ x) ≠ φ x := by sorry
