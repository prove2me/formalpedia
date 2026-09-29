-- Prove2me | solution 1 for mme_HasTauValueAtLeast_of_cofinal_finite_extractions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:47:34.695689+00:00
-- url     : https://prove2.me/submissions/39e401c7-abde-4503-839f-8dde40a0790f

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ) (hV : 0 ≤ V)
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hextract :
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            (T.kronPow (s n)) ∧
          V ^ (s n) * (1 - error n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast T tau V := by
  refine ⟨hV, ?_⟩
  intro epsilon hepsilon
  have herror_lt : ∀ᶠ n : ℕ in atTop, error n < epsilon :=
    (tendsto_order.1 herror).2 epsilon hepsilon
  have hsource : ∀ᶠ n : ℕ in atTop,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          (T.kronPow (s n)) ∧
        V ^ (s n) * (1 - epsilon) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
    filter_upwards [hextract, herror_lt] with n hn hnerror
    obtain ⟨k, a, b, c, hrestrict, hcount⟩ := hn
    refine ⟨k, a, b, c, hrestrict, ?_⟩
    calc
      V ^ (s n) * (1 - epsilon) ≤ V ^ (s n) * (1 - error n) := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_left hnerror.le 1) (pow_nonneg hV _)
      _ ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := hcount
  by_contra htarget
  rw [not_frequently] at htarget
  have hpullback := hs.eventually htarget
  obtain ⟨n, hn, hnot⟩ := (hsource.and hpullback).exists
  exact hnot hn
