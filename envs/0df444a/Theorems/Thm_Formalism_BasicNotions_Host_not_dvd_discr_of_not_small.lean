-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_not_dvd_discr_of_not_small
-- name    : Formalism.BasicNotions.Host.not_dvd_discr_of_not_small
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:24:55.356335+00:00
-- url     : https://prove2.me/theorems/1ad3765c-03d8-5b4d-b795-9fec797edfae
-- title:
--   Host: not dvd discr of not small
-- statement:
--   The Host construction uses the not dvd discr of not small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/HalfNorm.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/HalfNorm.lean#L16-L19

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

theorem Formalism.BasicNotions.Host.not_dvd_discr_of_not_small {p : ℕ} (hp : p.Prime) (h2 : p ∉ H.small) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    ¬ (p : ℤ) ∣ discr H.E := by sorry
