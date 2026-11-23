-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_formalSum_mem_integralSeries
-- name    : Formalism.ELL.WeierstrassChordSeries.formalSum_mem_integralSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:13.122452+00:00
-- url     : https://prove2.me/theorems/724bbc27-eded-4182-9e5c-81365910c2d5
-- title:
--   Weierstrass Chord Series: formal Sum mem integral Series
-- statement:
--   The Weierstrass Chord Series construction uses the formal Sum mem integral Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L619-L640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L619-L640

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

theorem Formalism.ELL.WeierstrassChordSeries.formalSum_mem_integralSeries (hw : WFixed W w) : F2 W w ∈ T W := by sorry
