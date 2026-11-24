-- Prove2me | Theorems.Thm_Formalism_PhiZ_analyticAt
-- name    : Formalism.PhiZ_analyticAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:08.99104+00:00
-- url     : https://prove2.me/theorems/9929f9d9-8c25-4472-831e-249d0df5ecae
-- title:
--   Formalism: Phi Z analytic At
-- statement:
--   The Formalism construction uses the Phi Z analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L105-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L105-L124

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
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
open Formalism
open ArithmeticFunction

theorem Formalism.PhiZ_analyticAt (ε C θ : ℝ) {s : ℂ} (hs0 : s ≠ 0)
    (hE : riemannZeta₁ s ≠ 0) (hsθ : s ≠ θ) : AnalyticAt ℂ (PhiZ ε C θ) s := by sorry
