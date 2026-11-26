-- Prove2me | Theorems.Thm_Eden_exponentSum_four_bound_and_eq
-- name    : Eden.exponentSum_four_bound_and_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:26.964186+00:00
-- url     : https://prove2.me/theorems/d617e411-3d13-4fc3-a645-8dd52b40c0b9
-- title:
--   Eden: exponent Sum four bound and eq
-- statement:
--   The Eden construction uses the exponent Sum four bound and eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L44-L61
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L44-L61

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_bound_and_eq {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    spectrumPartialSum (lyapunovExponent c p) 4 ≤ 4 ∧
      (spectrumPartialSum (lyapunovExponent c p) 4 = 4 ↔
        radiusSq₁ p = 1 ∧ radiusSq₂ p = 1) := by sorry
