-- Prove2me | Theorems.Thm_Formalism_rint_HZ
-- name    : Formalism.rint_HZ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:25.124924+00:00
-- url     : https://prove2.me/theorems/9dded00c-84da-41e1-b908-24ff0d508308
-- title:
--   Formalism: rint HZ
-- statement:
--   The Formalism construction uses the rint HZ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L63-L73

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

theorem Formalism.rint_HZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1) {σ : ℝ}
    (hσ : 1 < σ) : IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by sorry
