-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_coeff_mem
-- name    : Formalism.ELL.WeierstrassChordSeries.w_coeff_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:07.816343+00:00
-- url     : https://prove2.me/theorems/bb446c56-461b-402d-a878-83d97a3e2b13
-- title:
--   Weierstrass Chord Series: w coeff mem
-- statement:
--   The Weierstrass Chord Series construction uses the w coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L244-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L244-L254

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

theorem Formalism.ELL.WeierstrassChordSeries.w_coeff_mem {w : PowerSeries K} (hw : WFixed W w) (m : ℕ) :
    coeff m w ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) := by sorry
