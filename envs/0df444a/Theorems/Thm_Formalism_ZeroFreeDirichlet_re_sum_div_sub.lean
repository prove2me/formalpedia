-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_re_sum_div_sub
-- name    : Formalism.ZeroFreeDirichlet.re_sum_div_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:44:09.103318+00:00
-- url     : https://prove2.me/theorems/0aab40b4-e9d7-4181-962e-abf260e9c1bb
-- title:
--   Zero Free Dirichlet: re sum div sub
-- statement:
--   The Zero Free Dirichlet construction uses the re sum div sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L31-L35

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZerosOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.re_sum_div_sub (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)).re = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (z - ρ)).re := by sorry
