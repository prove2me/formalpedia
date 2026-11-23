-- Prove2me | Theorems.Thm_FRI_RBR_Soundness
-- name    : FRI_RBR_Soundness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:39:16.615109+00:00
-- url     : https://prove2.me/theorems/89ef99ba-1b39-4b28-bcb9-809027753703
-- title:
--   FRI RBR Soundness: FRI RBR Soundness
-- statement:
--   **Theorem 5.2: FRI Round-by-Round Soundness**
--
--   FRI has round-by-round soundness with a State function `FRI_State` and error functions
--   `ε^fold_i` and `ε^query` as described below.
--
--   **State Function** (defined as `FRI_State` in SimpleRbrFri.State):
--
--   **Main FRI Round-by-Round Soundness Theorem.**
--
--   This establishes that the FRI protocol has round-by-round soundness with state function σ
--   and error functions:
--   - **Folding rounds:** ε^fold_i(δ) = err*(C_i, m_i, δ*)
--   - **Query round:** ε^query(δ) = (1 - δ*)^t
--
--   **State Function σ:**
--
--   - **(Round 0) Empty transcript:** σ(f₀, ∅) = 1 iff f₀ ∈ C₀
--
--   - **(Rounds 1 to k) Folding rounds:** For round i ∈ [k], given transcript
--     tr = (α₁, f₁, ..., α_{i-1}, f_{i-1}) and verifier message α_i,
--     we set σ(f₀, tr || α_i) = 0 if there exists a set S ⊆ L_{i-1} such that:
--     (a) |S^{m_i}| ≥ (1 - δ*) · |L_i|  (large subset condition)
--     (b) Fold(f_{i-1}, m_i, α_i) agrees with some u' ∈ C_i on S^{m_i}
--     (c) f_{i-1} does NOT agree with any u ∈ C_{i-1} on S
--
--   - **(Round k+1) Query round:** σ(f₀, tr || s) = 1 iff:
--     1. The final prover message f_k ∈ C_k, and
--     2. For all query repetitions j and all rounds i, the local fold checks pass
--
--   **Error Bounds:**
--
--   - **Folding rounds:** Pr[σ(tr) = 0 ∧ σ(tr || α_i) = 1] ≤ ε^fold_i(δ) = err*(C_i, m_i, δ*)
--   - **Query round:** Pr[σ(tr) = 0 ∧ σ(tr || s) = 1] ≤ ε^query(δ) = (1 - δ*)^t
--
--   where:
--   - δ := Δ(f₀, C₀) is the relative distance from f₀ to code C₀
--   - δ* := min{δ, 1 - B(ρ) - 1/|L₀|} is the effective distance bound
--   - B(ρ) is the proximity bound for the powers generator
--   - err* is the error function from mutual correlated agreement
--   - t is the number of query repetitions
--
--   **Reference:** Theorem 5.2 (pages 15-16) - Main round-by-round soundness result.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L217-L268
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L217-L268

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]

theorem FRI_RBR_Soundness
    (P : FRIParameters F)
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (h_mca : FRI_MCA_Hypothesis P bound errorstar)
    (h_bound_valid : bound + 1 / P.D_0.card ≤ 1)
    (f_0 : P.D_0 → F) :
    -- Part 0: Initial State (Round 0)
    -- State(f_0, ∅) = 1 iff f_0 ∈ C_0
    (∀ T : FRITranscript P, FRI_State P f_0 bound T 0 ↔ f_0 ∈ (FRI_code P 0).carrier)
    ∧
    -- Part 1: Folding rounds (Rounds 1 to k)
    -- Pr[State(T, i) = 0 ∧ State(T || α, i+1) = 1] ≤ ε^fold_i(δ*)
    -- Note: IsFoldable and FRI_degree ≥ m are derived from FRIParameters
    (∀ T : FRITranscript P,
      ∀ i : Fin P.num_foldings,
      FRI_distance_star P f_0 bound < 1 - bound →
      0 ≤ FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound) →
      FRI_State_Transition_Prob_Fold P f_0 bound T i ≤
        FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound))
    ∧
    -- Part 2: Query round (Round k+1)
    -- Pr[State(T, k) = 0 ∧ State(T || s, k+1) = 1] ≤ (1 - δ*)^t
    -- Note: f_0 is now a separate parameter, not part of the transcript
    (∀ T : FRITranscript P,
      FRI_State_Transition_Prob_Query P f_0 bound T ≤
        ENNReal.ofReal ((1 - FRI_distance_star P f_0 bound) ^ P.q_rep)) := by sorry
