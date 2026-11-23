-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_formalSum
-- name    : Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:12.606614+00:00
-- url     : https://prove2.me/theorems/bbb9a76d-96d4-48d3-9fb9-01912318fab5
-- title:
--   Weierstrass Chord Series: linear Coeff formal Sum
-- statement:
--   The Weierstrass Chord Series construction uses the linear Coeff formal Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L537-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L537-L540

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

theorem Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum (hw : WFixed W w) (i : Fin 2) : (L i) (F2 W w) = 1 := by sorry
