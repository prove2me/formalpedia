-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_le_SS
-- name    : Formalism.HC.Der.Rd.le_SS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:50.708236+00:00
-- url     : https://prove2.me/theorems/85b9e1c3-85e5-425e-99fa-f8b59d45bb97
-- title:
--   Rd: le SS
-- statement:
--   The Rd construction uses the le SS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L314-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L314-L393

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)

theorem Formalism.HC.Der.Rd.le_SS {e d : ℕ} (h2 : 2 ^ (e + 2) ∣ N) (hd : d.Prime) (hdN : d ∣ N) (hd2 : ¬ 2 ∣ d)
    (hU : ∀ u ∈ U, ZMod.unitsMap h2 u = 1 ∨ ZMod.unitsMap h2 u = -1) (rd : 1 / 2 ≤ rho U (N / d)) :
    ((e : ℝ) + 1 - 1 / 2 ^ e) * Real.log 2 + Real.log d / 2 ≤ SS U := by sorry
