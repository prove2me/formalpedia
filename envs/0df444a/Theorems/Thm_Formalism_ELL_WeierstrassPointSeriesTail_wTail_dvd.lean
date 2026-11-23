-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassPointSeriesTail_wTail_dvd
-- name    : Formalism.ELL.WeierstrassPointSeriesTail.wTail_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:13.030519+00:00
-- url     : https://prove2.me/theorems/0d36fdba-8389-4859-88ca-90e487622f4f
-- title:
--   Weierstrass Point Series Tail: w Tail dvd
-- statement:
--   The Weierstrass Point Series Tail construction uses the w Tail dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WPoint.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WPoint.lean#L16-L24

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
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
open Formalism.ELL.WeierstrassPointSeriesTail

theorem Formalism.ELL.WeierstrassPointSeriesTail.wTail_dvd {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (k : ℕ) (hk : 1 ≤ k) (h : (X : PowerSeries R) ^ k ∣ w) :
    (X : PowerSeries R) ^ (k + 1) ∣ wTail W w := by sorry
