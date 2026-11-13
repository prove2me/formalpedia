-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_monotone_envelope_common_left_limit
-- name    : AvramDividend.Classical.avram_chat24_monotone_envelope_common_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:49:55.542175+00:00
-- url     : https://prove2.me/theorems/1dc83e67-4385-44b7-9c30-d94640d80bb1
-- title:
--   AvramDividend.Classical.avram_chat24_monotone_envelope_common_left_limit
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_monotone_envelope_common_left_limit from oversized parent candidate 5baa2fe7bf493330b9ddb51fde3c183478d7c2d2da01537e8cb97d7445aa9ced.
-- source:
--   candidate-decomposition:43452435-65f7-466e-8d89-977d504918f7:5baa2fe7bf493330b9ddb51fde3c183478d7c2d2da01537e8cb97d7445aa9ced

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem AvramDividend.Classical.avram_chat24_monotone_envelope_common_left_limit
    (f d : ℝ≥0 → ℝ) (hd : Monotone d) (t : ℝ≥0) (l x δ : ℝ)
    (hf : Tendsto f (𝓝[<] t) (nhds l))
    (hc : ContinuousWithinAt d (Iic t) t) :
    Tendsto (fun u => x + δ + f u - d u) (𝓝[<] t) (nhds (x + δ + l - d t)) ∧
    Tendsto (fun u => x + δ + f u - ⨅ s : Ioi u, d s)
      (𝓝[<] t) (nhds (x + δ + l - d t)) := by sorry
end
