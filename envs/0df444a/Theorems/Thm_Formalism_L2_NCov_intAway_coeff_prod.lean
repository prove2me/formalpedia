-- Prove2me | Theorems.Thm_Formalism_L2_NCov_intAway_coeff_prod
-- name    : Formalism.L2.NCov.intAway_coeff_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:24.032634+00:00
-- url     : https://prove2.me/theorems/056a6c62-c356-4f4a-997a-c40282e2fb3e
-- title:
--   NCov: int Away coeff prod
-- statement:
--   The NCov construction uses the int Away coeff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverVal.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverVal.lean#L115-L127

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Polynomial
variable {R : Type*} [CommRing R]
variable {q : R}

theorem Formalism.L2.NCov.intAway_coeff_prod (hq : IsIntegral ℤ q) (s : Multiset R) (hs : ∀ μ ∈ s, IntAway q μ) (n : ℕ) :
    IntAway q ((s.map fun μ => X - C μ).prod.coeff n) := by sorry
