-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_zerojump_ceiling_path_limit
-- name    : AvramDividend.Classical.avram_ubv_finite12_original_zerojump_ceiling_path_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:37:09.74402+00:00
-- url     : https://prove2.me/theorems/23b87d40-e005-490e-bd21-cdcc355b957d
-- title:
--   Original zero-jump Gaussian source converges along all shrinking upper stopping-clock meshes
-- statement:
--   On the source-probability-one event of global zero-jump Lévy path continuity, every sequence of upper physical clock approximations squeezed within mesh widths tending to zero converges to the true original stopped source. This covers any genuine sampled stopping ceilings constructed by the previous public lemma, without substituting an independent Brownian motion.
-- source:
--   Public Proved TOP11 original sample-path global continuity b462a147, pinned Mathlib topology squeeze theorem, and the exact original process X. The random grid ceilings are constrained only by their source-exact pathwise upper/lower bounds; the stochastic conditional-sampling step remains in public 6258d525.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_original_zerojump_ceiling_path_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (grid : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (nhds 0))
    (hBounds : ∀ n ω,
      σ ω ≤ grid n (K n ω) ∧ grid n (K n ω) ≤ σ ω + δ n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (grid n (K n ω)) ω)
        atTop (nhds (X.X (σ ω) ω)) := by sorry
