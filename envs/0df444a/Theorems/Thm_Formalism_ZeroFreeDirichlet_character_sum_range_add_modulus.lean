-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_character_sum_range_add_modulus
-- name    : Formalism.ZeroFreeDirichlet.character_sum_range_add_modulus
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:22.238854+00:00
-- url     : https://prove2.me/theorems/66834384-843f-454e-9579-331f5d88eb0c
-- title:
--   Zero Free Dirichlet: character sum range add modulus
-- statement:
--   The Zero Free Dirichlet construction uses the character sum range add modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean#L20-L24

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.character_sum_range_add_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ range (q + M), χ (n : ZMod q) = ∑ n ∈ range M, χ (n : ZMod q) := by sorry
