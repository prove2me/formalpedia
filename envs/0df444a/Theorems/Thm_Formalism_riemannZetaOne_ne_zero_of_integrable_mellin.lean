-- Prove2me | Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_integrable_mellin
-- name    : Formalism.riemannZetaOne_ne_zero_of_integrable_mellin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:33.680842+00:00
-- url     : https://prove2.me/theorems/91f67691-719f-491b-96c2-a4e87d08018f
-- title:
--   Formalism: riemann Zeta One ne zero of integrable mellin
-- statement:
--   The Formalism construction uses the riemann Zeta One ne zero of integrable mellin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L145-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L145-L206

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

theorem Formalism.riemannZetaOne_ne_zero_of_integrable_mellin (h1 : MellinDeriv) (h3 : MellinSgen) (h5 : MellinElem)
    (h11 : LogDerivZeroFree) {ε C θ : ℝ} (hε : ε * ε = 1) (hθ1 : θ < 1)
    (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x)
    (hInt : ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1)) :
    ∀ s : ℂ, θ < s.re → riemannZeta₁ s ≠ 0 := by sorry
