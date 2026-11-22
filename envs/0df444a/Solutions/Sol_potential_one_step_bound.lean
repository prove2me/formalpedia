-- Prove2me | solution 1 for potential_one_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:44.351708+00:00
-- url     : https://prove2.me/submissions/cfc6fd30-4cc7-4b3c-b559-48c32c49bff0

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Theorems.Thm_best_response_payoff_weights

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (cfg : MWUConfig C) :
    (mwuUpdateWeights M η hη1 cfg (hrow cfg.toPMF).choose).potential ≤
    cfg.potential * (1 - η * v) := by
  simp only [MWUConfig.potential, mwuUpdateWeights]
  -- LHS = Σ_c w(c) * (if M r c then 1-η else 1)
  -- We show this equals Φ - η * Σ_c w(c) * M(r,c)
  have hsum_eq : (∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then 1 - η else 1)) =
    (∑ c : C, cfg.weights c) -
    η * ∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) := by
    have : ∀ c : C, cfg.weights c *
        (if M (hrow cfg.toPMF).choose c then 1 - η else 1) =
      cfg.weights c - η * (cfg.weights c *
        (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) := by
      intro c; split_ifs <;> ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum_eq]
  -- RHS = Φ * (1 - ηv) = Φ - ηvΦ
  -- Need: Φ - η * S ≤ Φ - η * v * Φ, i.e., η * v * Φ ≤ η * S
  have hbr := best_response_payoff_weights M v hrow cfg
  -- hbr : v * Φ ≤ S where S = Σ_c w(c) · M(r,c)
  set S := ∑ c : C, cfg.weights c *
    (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) with hS_def
  -- From hbr: v * Φ ≤ S, so η * v * Φ ≤ η * S
  have h1 : η * (v * cfg.potential) ≤ η * S := mul_le_mul_of_nonneg_left hbr hη
  -- So Φ - η * S ≤ Φ - η * v * Φ = Φ * (1 - η * v)
  -- Unfold potential to make linarith see the connection
  unfold MWUConfig.potential at h1 hbr
  linarith
