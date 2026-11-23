-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_ne_zero_of_weq
-- name    : Formalism.ELL.WeierstrassSubstitution.ne_zero_of_weq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:36.410899+00:00
-- url     : https://prove2.me/theorems/6b36cd86-16da-4115-bca2-1d4f7232f437
-- title:
--   Weierstrass Substitution: ne zero of weq
-- statement:
--   The Weierstrass Substitution construction uses the ne zero of weq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSubst.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSubst.lean#L31-L34

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
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
open Formalism Formalism.ELL Formalism.ELL.WeierstrassSubstitution

theorem Formalism.ELL.WeierstrassSubstitution.ne_zero_of_weq {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s v : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s v) (hs : s ≠ 0) : v ≠ 0 := by sorry
