-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_fixed_unique
-- name    : Formalism.ELL.WeierstrassSeriesLimit.fixed_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:10.758585+00:00
-- url     : https://prove2.me/theorems/57353504-3c8e-4b55-9dfa-6b300300f07e
-- title:
--   Weierstrass Series Limit: fixed unique
-- statement:
--   The Weierstrass Series Limit construction uses the fixed unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L113-L123

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

theorem Formalism.ELL.WeierstrassSeriesLimit.fixed_unique {w w' : PowerSeries R} (hw : WFixed W w) (hw' : WFixed W w') : w = w' := by sorry
