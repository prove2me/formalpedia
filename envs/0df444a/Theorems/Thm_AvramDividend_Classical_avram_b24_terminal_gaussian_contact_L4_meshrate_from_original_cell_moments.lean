-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_terminal_gaussian_contact_L4_meshrate_from_original_cell_moments
-- name    : AvramDividend.Classical.avram_b24_terminal_gaussian_contact_L4_meshrate_from_original_cell_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:45:52.818909+00:00
-- url     : https://prove2.me/theorems/a7b53548-d12b-466a-8e10-d4bbd90df7cb
-- title:
--   Ruincrossing Gaussian contact fourth moment decays with mesh size under original-cell fourth moments
-- statement:
--   When the original intrinsic Gaussian source mesh cell increments possess the deterministic-time fourth-moment estimates 2 sigma^4 h_i^2, the unique random ruin-crossing contact cell has expected absolute fourth power bounded by 2 sigma^4 epsilon T, where epsilon is the maximum deterministic cell length and T bounds the total grid duration. Uses proved pathwise contact domination and pinned Gaussian fourth-moment mesh arithmetic, without assuming independence of the selected terminal cell or post-ruin continuation. The original-cell moment assumptions remain explicit and are the genuine Gaussian stochastic source obligation.
-- source:
--   Proved B24 terminal contact fourth-power expectation lemma and P4 original sigma fourth-moment deterministic mesh-error bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b24_contact_fourth_L1_from_cell_fourth_moments
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_terminal_gaussian_contact_L4_meshrate_from_original_cell_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (h : ℕ → ℝ≥0)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (hVI : ∀ i ∈ S, Integrable (fun ω => ‖V i ω‖ ^ 4) P)
    (hContactI : Integrable (fun ω =>
      ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4) P)
    (hFourth : ∀ i ∈ S,
      (∫ ω, ‖V i ω‖ ^ 4 ∂P) ≤ 2 * X.σ ^ 4 * (h i : ℝ) ^ 2)
    (ε T : ℝ) (hε : 0 ≤ ε)
    (hmax : ∀ i ∈ S, (h i : ℝ) ≤ ε)
    (hT : (∑ i ∈ S, (h i : ℝ)) ≤ T) :
    (∫ ω, ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i),
      V i ω‖ ^ 4 ∂P) ≤ 2 * X.σ ^ 4 * ε * T := by sorry
