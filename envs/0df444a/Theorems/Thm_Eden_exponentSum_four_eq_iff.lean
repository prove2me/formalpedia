-- Prove2me | Theorems.Thm_Eden_exponentSum_four_eq_iff
-- name    : Eden.exponentSum_four_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:42.237145+00:00
-- url     : https://prove2.me/theorems/618a9499-9d03-5986-877b-2cca169a9209
-- title:
--   Eden: exponent Sum four eq iff
-- statement:
--   The Eden construction uses the exponent Sum four eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L63-L68
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L63-L68

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_eq_iff {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ attractor) : spectrumPartialSum (lyapunovExponent c p) 4 = 4 ↔ p ∈ torus := by sorry
