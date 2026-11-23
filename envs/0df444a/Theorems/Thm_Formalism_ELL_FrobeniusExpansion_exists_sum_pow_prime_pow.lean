-- Prove2me | Theorems.Thm_Formalism_ELL_FrobeniusExpansion_exists_sum_pow_prime_pow
-- name    : Formalism.ELL.FrobeniusExpansion.exists_sum_pow_prime_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:55.806569+00:00
-- url     : https://prove2.me/theorems/5a74de39-af6a-4c1a-8abf-a206d2d23050
-- title:
--   Frobenius Expansion: exists sum pow prime pow
-- statement:
--   The Frobenius Expansion construction uses the exists sum pow prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsSumPowPrimePow.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsSumPowPrimePow.lean#L14-L26

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsSumPowPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.G
open Formalism.ELL.FrobeniusExpansion

theorem Formalism.ELL.FrobeniusExpansion.exists_sum_pow_prime_pow {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → A) (n : ℕ) :
    ∃ r : A, (∑ i ∈ s, f i) ^ (p ^ n) = ∑ i ∈ s, f i ^ (p ^ n) + (p : A) * r := by sorry
