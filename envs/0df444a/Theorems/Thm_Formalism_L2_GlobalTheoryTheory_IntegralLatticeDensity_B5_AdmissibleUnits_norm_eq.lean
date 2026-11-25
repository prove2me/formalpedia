-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_AdmissibleUnits_norm_eq
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.norm_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:56.443795+00:00
-- url     : https://prove2.me/theorems/ddfe6494-246e-4438-9ee6-15b41d595b7b
-- title:
--   Admissible Units: norm eq
-- statement:
--   The Admissible Units construction uses the norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/UnitsEqOneOrNegOne.lean#L62-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/UnitsEqOneOrNegOne.lean#L62-L81

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.norm_eq (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (α : K) : ((Algebra.norm ℚ α : ℚ) : ℝ) = ‖φ α‖ ^ 2 := by sorry
