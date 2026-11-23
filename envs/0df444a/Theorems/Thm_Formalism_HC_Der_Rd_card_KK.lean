-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_card_KK
-- name    : Formalism.HC.Der.Rd.card_KK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:26.182807+00:00
-- url     : https://prove2.me/theorems/eb2c4463-cc38-447a-acbf-5a38185f0edc
-- title:
--   Rd: card KK
-- statement:
--   The Rd construction uses the card KK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L180-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L180-L192

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
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
variable {N : ℕ} [NeZero N]

theorem Formalism.HC.Der.Rd.card_KK {f : ℕ} (hf : f ∣ N) : (KK N f).card * f.totient = N.totient := by sorry
