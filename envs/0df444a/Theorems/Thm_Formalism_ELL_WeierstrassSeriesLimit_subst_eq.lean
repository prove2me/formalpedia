-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_subst_eq
-- name    : Formalism.ELL.WeierstrassSeriesLimit.subst_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:25.50323+00:00
-- url     : https://prove2.me/theorems/f5d1070e-5b06-465d-aa5a-86c86448a4cd
-- title:
--   Weierstrass Series Limit: subst eq
-- statement:
--   The Weierstrass Series Limit construction uses the subst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L193-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L193-L201

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

theorem Formalism.ELL.WeierstrassSeriesLimit.subst_eq {w : PowerSeries R} (hw : WFixed W w) {σ : Type} (s : MvPowerSeries σ R)
    (hs : MvPowerSeries.constantCoeff s = 0) : WEqAt W s (w.subst s) := by sorry
