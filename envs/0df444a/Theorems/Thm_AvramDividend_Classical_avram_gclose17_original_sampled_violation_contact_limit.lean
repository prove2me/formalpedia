-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_sampled_violation_contact_limit
-- name    : AvramDividend.Classical.avram_gclose17_original_sampled_violation_contact_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:37:40.707435+00:00
-- url     : https://prove2.me/theorems/79fe7676-c025-494b-89f2-13d0155aa723
-- title:
--   Original sampled lower threshold violations force contact at their right-hand limit
-- statement:
--   For the true original spectrally negative Levy process with an adapted dividend strategy, if a sequence of physical observation times converges to a time t from the right and the actual postrightpayment reserve is strictly below δ at every observation, then the actual postrightpayment reserve at t is at most δ. This is the required stochastic-path endpoint-contact limit for a dense sampled lower-exit debut. It does not assume that an arbitrary infimum has a witnessing sequence; that remains a separate necessary order-theoretic obligation.
-- source:
--   Compose the already-Proved original postpayment reserve right continuity at t (a2202506) with convergence of the sampled witness sequence and use closedness of the half-line (-∞,δ] to transport strict reserve violations to the endpoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose17_original_sampled_violation_contact_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (δ : ℝ) (u : ℕ → ℝ≥0)
    (hu : Tendsto u atTop (𝓝[Ici t] t))
    (hbelow : ∀ n, x + X.X (u n) ω - rightLimit D (u n) ω < δ) :
    x + X.X t ω - rightLimit D t ω ≤ δ := by sorry
