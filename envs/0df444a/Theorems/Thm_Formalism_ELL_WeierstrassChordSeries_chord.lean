-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord
-- name    : Formalism.ELL.WeierstrassChordSeries.chord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:24.103697+00:00
-- url     : https://prove2.me/theorems/79852cd9-fcb3-4e48-99e2-fc83f2a7a553
-- title:
--   Weierstrass Chord Series: chord
-- statement:
--   The Weierstrass Chord Series construction uses the chord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L671-L770
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L671-L770

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

theorem Formalism.ELL.WeierstrassChordSeries.chord (hU : WSubstUnique.{u}) (hw : WFixed W w) :
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) (F2 W w) := by sorry
