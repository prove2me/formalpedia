-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_condN_le_four_sq
-- name    : Formalism.BasicNotions.Host.condN_le_four_sq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:24:47.77761+00:00
-- url     : https://prove2.me/theorems/88471e09-8b27-56e2-b47e-162ceefddbd9
-- title:
--   Host: cond N le four sq
-- statement:
--   The Host construction uses the cond N le four sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/HalfNorm.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/HalfNorm.lean#L94-L98

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_halfSupp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_HalfNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal
open scoped Pointwise
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)

theorem Formalism.BasicNotions.Host.condN_le_four_sq : ((H.QS : ℝ) * H.q * H.d) ≤ 4 * (R.n : ℝ) ^ 2 * H.q * H.d := by sorry
