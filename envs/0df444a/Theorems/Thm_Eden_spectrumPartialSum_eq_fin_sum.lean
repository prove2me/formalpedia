-- Prove2me | Theorems.Thm_Eden_spectrumPartialSum_eq_fin_sum
-- name    : Eden.spectrumPartialSum_eq_fin_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:40.238637+00:00
-- url     : https://prove2.me/theorems/42a44abb-a039-4bb6-948a-c0ff6e02573b
-- title:
--   Eden: spectrum Partial Sum eq fin sum
-- statement:
--   The Eden construction uses the spectrum Partial Sum eq fin sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L88-L94
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L88-L94

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.spectrumPartialSum_eq_fin_sum {k : ℕ} (hk : k ≤ 5) (a : Fin 5 → ℝ) :
    spectrumPartialSum a k = ∑ i : Fin k, a (Fin.castLE hk i) := by sorry
