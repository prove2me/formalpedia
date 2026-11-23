-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_fw_X_dvd
-- name    : Formalism.ELL.WeierstrassChordSeries.fw_X_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:24.046998+00:00
-- url     : https://prove2.me/theorems/d3f95b84-ea39-4c45-98ec-6e4d6cfc06fb
-- title:
--   Weierstrass Chord Series: fw X dvd
-- statement:
--   The Weierstrass Chord Series construction uses the fw X dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L194-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L194-L197

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

theorem Formalism.ELL.WeierstrassChordSeries.fw_X_dvd {v : PowerSeries K} (hv : X ∣ v) : X ∣ fw W v := by sorry
