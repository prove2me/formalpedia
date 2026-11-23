-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_v_ne_of_G
-- name    : Formalism.ELL.WeierstrassChordSeries.v_ne_of_G
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:20:25.508801+00:00
-- url     : https://prove2.me/theorems/82b44270-9ae3-4baf-b042-2d2cecdae601
-- title:
--   Weierstrass Chord Series: v ne of G
-- statement:
--   The Weierstrass Chord Series construction uses the v ne of G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L663-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L663-L669

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

theorem Formalism.ELL.WeierstrassChordSeries.v_ne_of_G (W : WeierstrassCurve K) {z v : MvPowerSeries (Fin 2) K} (hz : z ≠ 0)
    (hG : G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) z v = 0) : v ≠ 0 := by sorry
