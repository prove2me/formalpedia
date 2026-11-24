-- Prove2me | Theorems.Thm_Formalism_HC_Landau_PhiP_analyticAt
-- name    : Formalism.HC.Landau.PhiP_analyticAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:57.790296+00:00
-- url     : https://prove2.me/theorems/b381a00f-671c-4085-9a12-96b5c9087e61
-- title:
--   Landau: Phi P analytic At
-- statement:
--   The Landau construction uses the Phi P analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean#L95-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean#L95-L113

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction

theorem Formalism.HC.Landau.PhiP_analyticAt {P : ℂ → ℂ} (hP : Differentiable ℂ P) (a b : ℂ) (C θ : ℝ) {s : ℂ} (hs0 : s ≠ 0)
    (hE : P s ≠ 0) (hsθ : s ≠ θ) : AnalyticAt ℂ (PhiP P a b C θ) s := by sorry
