-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_T_sub
-- name    : Formalism.ELL.WeierstrassSeriesLimit.T_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:48.867226+00:00
-- url     : https://prove2.me/theorems/f38db15e-ab70-4410-b1fc-f680ccc471b6
-- title:
--   Weierstrass Series Limit: T sub
-- statement:
--   The Weierstrass Series Limit construction uses the T sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L25-L27

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

theorem Formalism.ELL.WeierstrassSeriesLimit.T_sub (a b : PowerSeries R) : T W a - T W b = (a - b) * E W a b := by sorry
