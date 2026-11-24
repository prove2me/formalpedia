-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_AdmissibleUnits_indep
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.indep
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:36:55.046535+00:00
-- url     : https://prove2.me/theorems/1ded2784-fcbe-48fd-8df1-522821d57cf0
-- title:
--   Admissible Units: indep
-- statement:
--   The Admissible Units construction uses the indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/UnitsEqOneOrNegOne.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/UnitsEqOneOrNegOne.lean#L13-L28

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.indep (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (a b : ℚ)
    (h : (a : K) + (b : K) * x = 0) : a = 0 ∧ b = 0 := by sorry
