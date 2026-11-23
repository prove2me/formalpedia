-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_lsq
-- name    : Formalism.ELL.FormalGroupPointsTorsion.lsq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:15.287922+00:00
-- url     : https://prove2.me/theorems/24b34c96-b5d9-4d8f-bf05-c304d73215e1
-- title:
--   Formal Group Points Torsion: lsq
-- statement:
--   The Formal Group Points Torsion construction uses the lsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L104-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L104-L113

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}

theorem Formalism.ELL.FormalGroupPointsTorsion.lsq {l a b : K} {M : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hM : 1 ≤ M)
    (h : ‖l ^ 2 + a * l - b‖ ≤ M) : ‖l‖ ^ 2 ≤ M := by sorry
