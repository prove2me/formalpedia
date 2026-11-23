-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_X_dvd_wMap
-- name    : Formalism.ELL.WeierstrassSeriesLimit.X_dvd_wMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:13.41994+00:00
-- url     : https://prove2.me/theorems/82eca30e-57de-49e7-a924-1f99f350d9fe
-- title:
--   Weierstrass Series Limit: X dvd w Map
-- statement:
--   The Weierstrass Series Limit construction uses the X dvd w Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L37-L42

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassSeriesLimit
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem Formalism.ELL.WeierstrassSeriesLimit.X_dvd_wMap {a : PowerSeries R} (ha : X ∣ a) : X ∣ T W a := by sorry
