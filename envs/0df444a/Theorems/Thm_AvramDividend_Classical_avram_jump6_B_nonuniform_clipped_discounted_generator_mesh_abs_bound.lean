-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_nonuniform_clipped_discounted_generator_mesh_abs_bound
-- name    : AvramDividend.Classical.avram_jump6_B_nonuniform_clipped_discounted_generator_mesh_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:03:07.485357+00:00
-- url     : https://prove2.me/theorems/861eb1ba-d3df-464d-976a-6260631e54c3
-- title:
--   Uniform horizon bound for nonuniform clipped discounted HJB generator physical mesh
-- statement:
--   The signed absolute generator mesh sum over any monotone nonuniform stopped grid has a uniform T*B bound when every discounted weight lies in [0,1] and every generator integrand has absolute value ≤B. The grid increments telescope exactly. This supports L1 domination of true finite stopped physical generator sums under localisation and a source-proved compact generator envelope, without assuming equal cell widths.

import Mathlib
open MeasureTheory Set
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_nonuniform_clipped_discounted_generator_mesh_abs_bound
    (m : ℕ) (v : ℕ → ℝ)
    (hv : Monotone v) (hv0 : v 0 = 0)
    (T : ℝ) (hT : v m ≤ T)
    (B : ℝ) (hB : 0 ≤ B)
    (E F : ℕ → ℝ)
    (hE : ∀ i < m, 0 ≤ E i ∧ E i ≤ 1)
    (hF : ∀ i < m, |F i| ≤ B) :
    |∑ i ∈ Finset.range m,
      E i * (v (i + 1) - v i) * F i| ≤ T * B := by sorry
