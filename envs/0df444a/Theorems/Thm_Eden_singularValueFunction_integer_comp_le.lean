-- Prove2me | Theorems.Thm_Eden_singularValueFunction_integer_comp_le
-- name    : Eden.singularValueFunction_integer_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:36:57.744964+00:00
-- url     : https://prove2.me/theorems/3ffdc103-0cfd-407f-90f7-6e6157d55b3a
-- title:
--   Eden: singular Value Function integer comp le
-- statement:
--   The integer product is submultiplicative for arbitrary ambient maps,
--   including singular maps.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L25-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L25-L31

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.singularValueFunction_integer_comp_le {k : ℕ} (hk : k ≤ 5)
    (A B : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction (A ∘ₗ B) k ≤ singularValueFunction A k * singularValueFunction B k := by sorry
