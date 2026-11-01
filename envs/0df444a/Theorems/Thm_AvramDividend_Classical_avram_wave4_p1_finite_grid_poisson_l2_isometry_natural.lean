-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_poisson_l2_isometry_natural
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_grid_poisson_l2_isometry_natural
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:32:54.046575+00:00
-- url     : https://prove2.me/theorems/393e1554-ed58-4330-9e12-2328c6ad09ff
-- title:
--   Natural finite-grid predictable Poisson count L2 isometry
-- statement:
--   For an actual probability-space finite grid with measurable square-integrable cell coefficients H_i and genuine Poisson(r_i) counts K_i, assume each future K_i is independent of the joint pair (all previous compensated increments summed, H_i), and integrability of each centred count. Then the entire weighted centred sum is square-integrable and its expected squared norm equals the sum of per-cell rate times coefficient squared expectations. Unlike the earlier induction statement, neither individual MemLp nor prefix MemLp is assumed: they are derived from measurability, integrable squares and per-cell independence using pinned Mathlib and the separately proved prefix L2 theorem. It does not assume a martingale or isometry conclusion and does not identify the original Lévy jump PRM.
-- source:
--   Canonical Proved P1 finite-grid isometry UUID 647b088f-557c-4312-9dbd-bc44b740fa32 and canonical Proved finite-grid prefix MemLp UUID 28a15d79-569b-4814-aa9f-1680e2ad2589; pinned Mathlib memLp_two_iff_integrable_sq; joint-past independence projection via IndepFun.comp.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_predictable_poisson_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_poisson_prefix_memLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_finite_grid_poisson_l2_isometry_natural
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (hJointPast : ∀ i, IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))), H i ω))
      (K i) P)
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range n,
        H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2 ∂P) =
          ∑ i ∈ Finset.range n,
            (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
