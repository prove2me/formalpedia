-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_weq_iff
-- name    : Formalism.ELL.WeierstrassChordSeries.weq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:59.170236+00:00
-- url     : https://prove2.me/theorems/8bdef08e-94e2-43ba-944d-af32b65e65f2
-- title:
--   Weierstrass Chord Series: weq iff
-- statement:
--   The Weierstrass Chord Series construction uses the weq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L642-L649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L642-L649

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
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
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}

theorem Formalism.ELL.WeierstrassChordSeries.weq_iff (W : WeierstrassCurve K) (s v : MvPowerSeries (Fin 2) K) :
    WEqAt W s v ↔ G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) s v = 0 := by sorry
