-- Prove2me | Theorems.Thm_Formalism_landauIteratedDerivatives_meas_rpow
-- name    : Formalism.landauIteratedDerivatives.meas_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:19.930595+00:00
-- url     : https://prove2.me/theorems/1519eef4-69a9-4506-a08f-0c631ef9cb9e
-- title:
--   landau Iterated Derivatives: meas rpow
-- statement:
--   The landau Iterated Derivatives construction uses the meas rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L14-L16

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

theorem Formalism.landauIteratedDerivatives.meas_rpow (H : ℝ → ℝ) (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (σ : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => H x * x ^ (-σ - 1)) (volume.restrict (Ioi 1)) := by sorry
