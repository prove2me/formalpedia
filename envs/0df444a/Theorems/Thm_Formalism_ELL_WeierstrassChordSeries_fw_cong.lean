-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_fw_cong
-- name    : Formalism.ELL.WeierstrassChordSeries.fw_cong
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:13.865573+00:00
-- url     : https://prove2.me/theorems/19b93a4c-8f8f-4ace-8863-a02081e90c69
-- title:
--   Weierstrass Chord Series: fw cong
-- statement:
--   The Weierstrass Chord Series construction uses the fw cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L183-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L183-L192

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

theorem Formalism.ELL.WeierstrassChordSeries.fw_cong {n : ℕ} {v v' : PowerSeries K} (h : X ^ n ∣ v - v') (hv : X ∣ v) (hv' : X ∣ v') :
    X ^ (n + 1) ∣ fw W v - fw W v' := by sorry
