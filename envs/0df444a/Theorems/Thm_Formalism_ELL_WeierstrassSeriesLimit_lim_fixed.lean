-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_lim_fixed
-- name    : Formalism.ELL.WeierstrassSeriesLimit.lim_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:12.904802+00:00
-- url     : https://prove2.me/theorems/443bee62-698d-4587-864a-28ca70e01838
-- title:
--   Weierstrass Series Limit: lim fixed
-- statement:
--   The Weierstrass Series Limit construction uses the lim fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L91-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L91-L111

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

theorem Formalism.ELL.WeierstrassSeriesLimit.lim_fixed : WFixed W (lim W) := by sorry
