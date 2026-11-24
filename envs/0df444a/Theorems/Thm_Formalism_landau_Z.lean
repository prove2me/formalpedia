-- Prove2me | Theorems.Thm_Formalism_landau_Z
-- name    : Formalism.landau_Z
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:21.864437+00:00
-- url     : https://prove2.me/theorems/0c55e439-d8fb-4675-b1af-94c8b350fb97
-- title:
--   Formalism: landau Z
-- statement:
--   The Formalism construction uses the landau Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L126-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L126-L143

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

theorem Formalism.landau_Z (h2 : LandauEq) (h3 : MellinSgen) (h5 : MellinElem) (h8 : ZetaRealNonvanish)
    {ε C θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x) :
    ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by sorry
