-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Fm_abs_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Fm_abs_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:04.219026+00:00
-- url     : https://prove2.me/theorems/8aa4685c-c4c6-472c-8c0d-d5c843576e68
-- title:
--   Primes In Progressions: Fm abs le
-- statement:
--   The Primes In Progressions construction uses the Fm abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L169-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L169-L186

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Fm_abs_le {K θ β t : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (ht : 1 ≤ t) : |Fm K θ β t| ≤ 3 * t := by sorry
