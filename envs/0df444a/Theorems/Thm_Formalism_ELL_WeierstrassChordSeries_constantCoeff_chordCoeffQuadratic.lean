-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_chordCoeffQuadratic
-- name    : Formalism.ELL.WeierstrassChordSeries.constantCoeff_chordCoeffQuadratic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:11.419718+00:00
-- url     : https://prove2.me/theorems/781a77c3-03e6-4dfd-8794-35a172ac06eb
-- title:
--   Weierstrass Chord Series: constant Coeff chord Coeff Quadratic
-- statement:
--   The Weierstrass Chord Series construction uses the constant Coeff chord Coeff Quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L502-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L502-L503

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

theorem Formalism.ELL.WeierstrassChordSeries.constantCoeff_chordCoeffQuadratic (hw : WFixed W w) : cc (C2 W w) = 0 := by sorry
