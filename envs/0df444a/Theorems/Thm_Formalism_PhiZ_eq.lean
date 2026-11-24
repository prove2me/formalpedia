-- Prove2me | Theorems.Thm_Formalism_PhiZ_eq
-- name    : Formalism.PhiZ_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:19.984174+00:00
-- url     : https://prove2.me/theorems/ac55379b-f2c4-4bbc-88da-7810bd4f936b
-- title:
--   Formalism: Phi Z eq
-- statement:
--   The Formalism construction uses the Phi Z eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L93-L98

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

theorem Formalism.PhiZ_eq {ε C θ : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hZ : riemannZeta₁ s ≠ 0) :
    PhiZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by sorry
