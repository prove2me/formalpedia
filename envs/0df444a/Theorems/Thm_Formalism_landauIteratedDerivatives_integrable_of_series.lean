-- Prove2me | Theorems.Thm_Formalism_landauIteratedDerivatives_integrable_of_series
-- name    : Formalism.landauIteratedDerivatives.integrable_of_series
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:13.860278+00:00
-- url     : https://prove2.me/theorems/9148b8b6-bb1b-4fca-8745-bb38ccd4644f
-- title:
--   landau Iterated Derivatives: integrable of series
-- statement:
--   The landau Iterated Derivatives construction uses the integrable of series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L149-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L149-L201

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
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
open Formalism.landauIteratedDerivatives

theorem Formalism.landauIteratedDerivatives.integrable_of_series {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x) {cr t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-cr - 1))) (Ioi 1))
    (hsum : Summable (fun n : ℕ =>
      ∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))))) :
    Good H (cr - t) := by sorry
