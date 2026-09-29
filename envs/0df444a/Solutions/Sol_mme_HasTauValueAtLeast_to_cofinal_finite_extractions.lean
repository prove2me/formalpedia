-- Prove2me | solution 1 for mme_HasTauValueAtLeast_to_cofinal_finite_extractions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:03:11.750639+00:00
-- url     : https://prove2.me/submissions/6ef70efe-9f38-47d5-8201-e963547a2cf5

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

/-!
# Selecting a cofinal sequence from a tau-value witness

The definition provides a frequent set of usable powers for every positive
error.  Choosing one power beyond `n` at error `1/(n+1)` gives a cofinal
sequence with vanishing error and retains every concrete restriction.
-/

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ)
    (hV : HasTauValueAtLeast T tau V) :
    ∃ (s : ℕ → ℕ) (error : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      (∀ n, 0 < error n) ∧
      ∀ n,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            (T.kronPow (s n)) ∧
          V ^ (s n) * (1 - error n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  let error : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have herror_pos : ∀ n, 0 < error n := by
    intro n
    dsimp [error]
    positivity
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error, Function.comp_def] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
  have hextract : ∀ n : ℕ,
      ∃ N : ℕ, n ≤ N ∧
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            (T.kronPow N) ∧
          V ^ N * (1 - error n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
    intro n
    have hwitness := hV.2 (error n) (herror_pos n)
    have hlarge : ∀ᶠ N : ℕ in atTop, n ≤ N := eventually_ge_atTop n
    exact (hwitness.and_eventually hlarge).exists.imp fun N hN =>
      ⟨hN.2, hN.1⟩
  choose s hs using hextract
  have hs_tendsto : Tendsto s atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (hs n).1
  exact ⟨s, error, hs_tendsto, herror, herror_pos, fun n => (hs n).2⟩
