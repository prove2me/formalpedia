-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_clock_reserve_atom_sequence
-- name    : AvramDividend.Classical.avram_chat24_positive_clock_reserve_atom_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:53:13.172742+00:00
-- url     : https://prove2.me/theorems/bbdeb239-fa62-4674-8f39-72823f3d16ce
-- title:
--   AvramDividend.Classical.avram_chat24_positive_clock_reserve_atom_sequence
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_positive_clock_reserve_atom_sequence from oversized parent candidate 8100162f9276db8193c0346a4c3c0281bea466046ede13a673b6021f3586738a.
-- source:
--   candidate-decomposition:43452435-65f7-466e-8d89-977d504918f7:8100162f9276db8193c0346a4c3c0281bea466046ede13a673b6021f3586738a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem AvramDividend.Classical.avram_chat24_positive_clock_reserve_atom_sequence
    (f d : ℝ≥0 → ℝ) (hd : Monotone d) (t : ℝ≥0) (ht : 0 < t)
    (hc : ContinuousWithinAt d (Iic t) t) (l x δ q a b : ℝ)
    (hf : Tendsto f (𝓝[<] t) (nhds l)) (hδ : 0 < δ)
    (hpre : ∀ u, 0 < u → u < t → 0 ≤ x + f u - d u)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (hn : ∀ y, 0 ≤ w y) :
    let Y := Function.leftLim (fun u => x + δ + f u - ⨅ s : Ioi u, d s) t
    let z := f t - Function.leftLim f t
    let J := if Y ∈ Icc a b ∧ z < 0 then
      Real.exp (-(q * (t : ℝ))) * (w (Y + z) - w Y) else 0
    ∃ (u : ℕ → ℝ≥0) (v : ℝ),
      (∀ n, 0 < u n ∧ u n < t) ∧ Monotone u ∧ Tendsto u atTop (nhds t) ∧
      Tendsto (fun n => Real.exp (-(q * (u n : ℝ))) * w (x + f (u n) - d (u n) + δ))
        atTop (nhds v) ∧ 0 ≤ v + J := by sorry
end
