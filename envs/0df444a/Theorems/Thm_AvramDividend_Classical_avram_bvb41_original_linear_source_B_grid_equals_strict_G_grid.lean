-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb41_original_linear_source_B_grid_equals_strict_G_grid
-- name    : AvramDividend.Classical.avram_bvb41_original_linear_source_B_grid_equals_strict_G_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:24:08.208516+00:00
-- url     : https://prove2.me/theorems/54acd27c-2ce3-49dc-9bec-4d52fd5cf67c
-- title:
--   On original linear no-source-jump physical paths the complete source HJB grid B equals its strict-interior generator grid G
-- statement:
--   For the exact original bounded-variation Lévy path X_t=t*drift through physical horizon S, the complete source hB grid includes the strict-interior generator term G_n and the auxiliary stochastic-noise correction sum Σ coeff_i(R(u_i)-R(u_{i+1})). The original R_t is precisely t*drift-X_t minus the entire source left-limit negative jump compensated series. On this genuine original no-source-jump path every R_t=0 through S by published bvb40. Provided the source grid cell endpoints all lie in the original horizon, the auxiliary noise correction is zero for each cell regardless of its original generator coefficient. Thus the original actual B_n equals G_n at every n. This lets authoritative hAllB≤0 imply actual strict generator G_n≤0 on the mixed-reserve survivor route.
-- source:
--   Exact original hB decomposition in 540ad469 / b2d827e6; direct original source residual atom bvb40.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb40_original_linear_source_compensated_jump_residual_identically_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb41_original_linear_source_B_grid_equals_strict_G_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (S : ℝ≥0)
    (hSource : ∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift)
    (u : ℕ → ℕ → ℝ≥0)
    (hCells : ∀ n i, i ≤ n + 1 → u n i ≤ S)
    (R : ℝ≥0 → ℝ)
    (hR : ∀ t : ℝ≥0, t ≤ S →
      R t = ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0))
    (coeff : ℕ → ℕ → ℝ) (B G : ℕ → ℝ)
    (hB : ∀ n, B n = G n +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i * (R (u n i) - R (u n (i + 1))))) :
    ∀ n, B n = G n := by sorry
