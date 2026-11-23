-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constSeries_mem_integralSeries
-- name    : Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:57.438367+00:00
-- url     : https://prove2.me/theorems/42d602fb-06b8-4a7e-9676-6c7bf837ee77
-- title:
--   Weierstrass Chord Series: const Series mem integral Series
-- statement:
--   The Weierstrass Chord Series construction uses the const Series mem integral Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L592-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L592-L600

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

theorem Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries {a : K} (ha : a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) : ca a ∈ T W := by sorry
