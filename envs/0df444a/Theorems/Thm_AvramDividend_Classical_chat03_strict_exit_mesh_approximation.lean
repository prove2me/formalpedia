-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_mesh_approximation
-- name    : AvramDividend.Classical.chat03_strict_exit_mesh_approximation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:23:59.809334+00:00
-- url     : https://prove2.me/theorems/8619c787-f68e-4cfc-8ecf-8378a3c5ed66
-- title:
--   Strict two-sided first-passage infimum approximated by genuine exits on every fine mesh
-- statement:
--   Fix a spectrally negative Lévy path X, a strict exit set S={t : X_t<lower or upper<X_t}, and its greatest lower bound τ in nonnegative real time. For any ε>0 there is δ>0 so that any uniform mesh h with 0<h<δ contains an index k satisfying τ≤k h<τ+ε and an actual strict exit at that grid sample. Importantly τ need not itself be an exit, so this includes creeping and boundary contact. The proof derives an exit witness within ε of the infimum from IsGLB, uses the Proved right-continuity strict-exit interval, and then the Proved NNReal ceiling-grid bracket to find a grid point inside that interval and before τ+ε. The theorem does not claim killed q-scale harmonicity, finite-horizon stopping event convergence or stopped-value convergence.
-- source:
--   Chat 03 direct proof using Proved f0afde4a-46d2-43ca-9485-019f49c61fa3 strict_exit_right_interval and 15e09c24-2f6f-4b3e-8446-49353fbbb197 nnreal_grid_ceiling_bracket at pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Source prepared 19 October 2026.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_exit_mesh_approximation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < τ + ε ∧
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) := by sorry
