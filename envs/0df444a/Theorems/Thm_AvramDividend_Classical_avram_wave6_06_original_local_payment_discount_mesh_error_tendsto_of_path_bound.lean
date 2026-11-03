-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
-- name    : AvramDividend.Classical.avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:15:59.705872+00:00
-- url     : https://prove2.me/theorems/54bf2416-8cb8-4b77-87cc-c3a34cf7a606
-- title:
--   Actual controlled Lévy local pre/postpayment discount mesh error vanishes along bounded fine grids
-- statement:
--   For the same original spectrally negative Lévy sample path and left-continuous dividends, the discounted absolute pre/postpayment value-gap mesh sum tends to zero if both reserves stay in one compact interval on which w is L-Lipschitz, the grid widths tend to zero and the total dividend right-limit increment is uniformly bounded along the grids. An exact deterministic successor to Proved Chat09 local mesh gap 3c4bf891; it does not assume any Gaussian/jump stochastic identity.
-- source:
--   Avram Proposition 4(i), Eq. (5.11)-(5.13), payment discount timing error; Proved 3c4bf891 local Lipschitz gap

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ L * |s - t|)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (hPre : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω ∈ Icc a b)
    (htotal : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (u n (k n)) ω - rightLimit D (u n 0) ω ≤ B)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∑ i ∈ Finset.range (k n),
        (Real.exp (-(q * (u n i : ℝ))) -
          Real.exp (-(q * (u n (i + 1) : ℝ)))) *
          |w (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
            w (x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω)|)
      atTop (𝓝 0) := by sorry
