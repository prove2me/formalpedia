-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_low
-- name    : Formalism.ELL.WeierstrassChordSeries.w_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:17.752813+00:00
-- url     : https://prove2.me/theorems/18d82705-510c-4324-8589-3f9e508a3132
-- title:
--   Weierstrass Chord Series: w low
-- statement:
--   The Weierstrass Chord Series construction uses the w low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L256-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L256-L275

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
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
variable {W}

theorem Formalism.ELL.WeierstrassChordSeries.w_low {w : PowerSeries K} (hw : WFixed W w) :
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1 := by sorry
