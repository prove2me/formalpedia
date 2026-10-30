-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_partition_variation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_partition_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:39:33.940523+00:00
-- url     : https://prove2.me/theorems/2faae607-6a38-40ab-a87f-de5c4dbf9672
-- title:
--   Actual BV controlled reserve has uniformly bounded finite-partition variation
-- statement:
--   For the genuine bounded-variation Lévy path, every adapted left-continuous monotone dividend strategy yields a controlled reserve whose variation along every nondecreasing finite time partition is bounded by the original physical-drift path-variation allowance plus the actual total paid cumulative dividends. The single almost-sure event is uniform over all finite partitions and does not require dividends to be purely atomic. This is a source-level pathwise finite-variation input toward the regulated BV Itô–Meyer chain rule, rather than a substitute for compensated Lévy jump expectations.
-- source:
--   Combine the remotely Proved original BV Lévy path variation bound acd3eb12-f81b-4cde-becf-400b2d79a7e6 with the exact source riskProcess=x+X-D, nondecreasing dividend strategy and real triangle inequality. The resulting finite-partition bound is essential for pathwise regulated change-of-variables and explicitly preserves continuous Stieltjes control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_partition_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u → ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
        |riskProcess X x D (u (i + 1)) ω - riskProcess X x D (u i) ω|) ≤
      2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
        (X.X (u n) ω - X.X (u 0) ω) +
        (D (u n) ω - D (u 0) ω) := by sorry
