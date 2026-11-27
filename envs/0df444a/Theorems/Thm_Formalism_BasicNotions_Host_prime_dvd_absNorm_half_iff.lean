-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_prime_dvd_absNorm_half_iff
-- name    : Formalism.BasicNotions.Host.prime_dvd_absNorm_half_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:41:42.483689+00:00
-- url     : https://prove2.me/theorems/435d9766-d0de-48df-9d6c-9fdcb6ab5f33
-- title:
--   Host: prime dvd abs Norm half iff
-- statement:
--   The Host construction uses the prime dvd abs Norm half iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/HalfNorm.lean#L57-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/HalfNorm.lean#L57-L83

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

theorem Formalism.BasicNotions.Host.prime_dvd_absNorm_half_iff {p : ℕ} (hp : p.Prime) : p ∣ absNorm H.𝔟 ↔ p ∣ H.QS * H.q := by sorry
