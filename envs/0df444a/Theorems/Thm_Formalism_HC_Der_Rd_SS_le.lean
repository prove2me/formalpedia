-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_SS_le
-- name    : Formalism.HC.Der.Rd.SS_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:56.727355+00:00
-- url     : https://prove2.me/theorems/c5f626a7-50df-44a6-98eb-a7a5bcce5ee2
-- title:
--   Rd: SS le
-- statement:
--   The Rd construction uses the SS le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L111-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L111-L166

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

theorem Formalism.HC.Der.Rd.SS_le {q d : ℕ} (h2 : 2 ∣ N) (hq : q.Prime) (hd : d.Prime) (hqN : q ∣ N) (hdN : d ∣ N) (hq2 : ¬ 2 ∣ q)
    (hd2 : ¬ 2 ∣ d) (hqd : q ≠ d) (rq : rho U (N / q) ≤ 1 / 2) (rd : rho U (N / d) ≤ 1 / 2) :
    SS U ≤ Real.log N - Real.log 2 - Real.log q / 2 - Real.log d / 2 := by sorry
