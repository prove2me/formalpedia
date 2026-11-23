-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_ne_zero_of_L
-- name    : Formalism.ELL.WeierstrassChordSeries.ne_zero_of_L
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:13.667802+00:00
-- url     : https://prove2.me/theorems/da25cb6b-9ec4-4de9-a9ef-c40a6a110df6
-- title:
--   Weierstrass Chord Series: ne zero of L
-- statement:
--   The Weierstrass Chord Series construction uses the ne zero of L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L659-L661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L659-L661

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

theorem Formalism.ELL.WeierstrassChordSeries.ne_zero_of_L {φ : MvPowerSeries (Fin 2) K} {i : Fin 2} (h : (L i) φ ≠ 0) : φ ≠ 0 := by sorry
