-- Prove2me | Theorems.Thm_Formalism_landauIteratedDerivatives_good_logpow
-- name    : Formalism.landauIteratedDerivatives.good_logpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:48.990104+00:00
-- url     : https://prove2.me/theorems/a2ed80e6-ebcb-49d7-95a7-96d355d8f736
-- title:
--   landau Iterated Derivatives: good logpow
-- statement:
--   The landau Iterated Derivatives construction uses the good logpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L50-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L50-L74

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

theorem Formalism.landauIteratedDerivatives.good_logpow {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    {τ σ : ℝ} (hτ : Good H τ) (hlt : τ < σ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-σ - 1))) (Ioi 1) := by sorry
