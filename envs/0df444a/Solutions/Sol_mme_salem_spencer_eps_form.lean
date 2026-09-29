-- Prove2me | solution 1 for mme_salem_spencer_eps_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T19:06:47.492931+00:00
-- url     : https://prove2.me/submissions/0a8f3bc9-a654-40ee-846c-83531015b231

import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

/-- **Salem–Spencer subsets are asymptotically dense.**

For every `ε > 0`, there is a threshold `N₀` past which the integer interval
`{0, 1, …, N-1}` contains a 3-term-AP-free Finset of cardinality at least
`N^{1-ε}`.

  `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∃ S ⊆ Finset.range N,
       ThreeAPFree (S : Set ℕ) ∧ N^(1-ε) ≤ S.card`.

This is the canonical **ε-form** of Salem–Spencer / Behrend density bounds
used by every laser-method argument: Coppersmith–Winograd 1990,
Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, etc.

**Proof outline.** Combine three ingredients from `Mathlib`:

1. `Behrend.roth_lower_bound` gives the explicit lower bound
   $\text{rothNumberNat}(N) \geq N \cdot \exp(-4\sqrt{\log N})$.

2. For $N \geq \exp(16/\varepsilon^2)$, the inequality
   $\exp(-4\sqrt{\log N}) \geq N^{-\varepsilon}$ holds (because
   $-4\sqrt{\log N} \geq -\varepsilon \log N$ when $\sqrt{\log N} \geq 4/\varepsilon$).

3. By definition, $\text{rothNumberNat}(N)$ is the cardinality of a maximal
   3AP-free Finset subset of `Finset.range N`; extract that witness.

**Reusability.** This is one of the two most reusable Layer-3 leaves — every
laser-method ω-bound uses exactly this ε-form. Stating it as a single
abstract theorem here factors out the Mathlib bridge that future agents
would otherwise rewrite per paper. -/
theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ S : Finset ℕ, S ⊆ Finset.range N ∧
        ThreeAPFree (S : Set ℕ) ∧ (N : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by
  -- The threshold: N ≥ exp(16/ε²), and at least 2 so log N ≥ log 2 > 0.
  refine ⟨max 2 (Nat.ceil (Real.exp (16 / ε ^ 2)) + 1), ?_⟩
  intro N hN
  -- Basic bounds.
  have hN2 : (2 : ℕ) ≤ N := le_trans (le_max_left _ _) hN
  have hNceil : Nat.ceil (Real.exp (16 / ε ^ 2)) + 1 ≤ N :=
    le_trans (le_max_right _ _) hN
  -- N ≥ 1 as a real.
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hN0R : (0 : ℝ) < (N : ℝ) := by linarith
  -- ε² > 0.
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  -- N as real ≥ exp(16/ε²).
  have hexp_pos : (0 : ℝ) < Real.exp (16 / ε ^ 2) := Real.exp_pos _
  have hN_ge_exp : Real.exp (16 / ε ^ 2) ≤ (N : ℝ) := by
    have hceil : Real.exp (16 / ε ^ 2) ≤ (Nat.ceil (Real.exp (16 / ε ^ 2)) : ℝ) :=
      Nat.le_ceil _
    have hstep : (Nat.ceil (Real.exp (16 / ε ^ 2)) : ℝ) ≤ (N : ℝ) := by
      have : Nat.ceil (Real.exp (16 / ε ^ 2)) ≤ N := by
        have := hNceil
        omega
      exact_mod_cast this
    linarith
  -- Therefore log N ≥ 16/ε².
  have hlogN_ge : 16 / ε ^ 2 ≤ Real.log (N : ℝ) := by
    have h := (Real.log_le_log_iff hexp_pos hN0R).mpr hN_ge_exp
    rwa [Real.log_exp] at h
  -- log N > 0.
  have hlogN_pos : 0 < Real.log (N : ℝ) := by
    have h16 : (0 : ℝ) < 16 / ε ^ 2 := by positivity
    linarith
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := le_of_lt hlogN_pos
  -- sqrt log N ≥ 4/ε.
  have h4eps_nn : (0 : ℝ) ≤ 4 / ε := by positivity
  have hsqrt_ge : 4 / ε ≤ Real.sqrt (Real.log (N : ℝ)) := by
    have hsq : (4 / ε) ^ 2 = 16 / ε ^ 2 := by
      field_simp
      ring
    have h1 : (4 / ε) ^ 2 ≤ Real.log (N : ℝ) := by rw [hsq]; exact hlogN_ge
    -- sqrt (x^2) = x when x ≥ 0; and sqrt is monotone.
    have h2 : Real.sqrt ((4 / ε) ^ 2) ≤ Real.sqrt (Real.log (N : ℝ)) :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq h4eps_nn] at h2
  have hsqrt_nn : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  -- ε * log N ≥ 4 * sqrt(log N): multiply sqrt_ge by sqrt(log N) ≥ 0.
  have hsq_sqrt : Real.sqrt (Real.log (N : ℝ)) ^ 2 = Real.log (N : ℝ) :=
    Real.sq_sqrt hlogN_nn
  have hmul_ineq : 4 * Real.sqrt (Real.log (N : ℝ)) ≤ ε * Real.log (N : ℝ) := by
    -- From 4/ε ≤ sqrt(log N), multiply both sides by ε > 0:
    -- 4 ≤ ε * sqrt(log N). Then multiply both sides by sqrt(log N).
    have h1 : 4 ≤ ε * Real.sqrt (Real.log (N : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hsqrt_ge (le_of_lt hε)
      have heq : ε * (4 / ε) = 4 := by field_simp
      linarith [this, heq.le, heq.ge]
    -- Multiply by sqrt(log N) ≥ 0.
    have h2 : 4 * Real.sqrt (Real.log (N : ℝ)) ≤
              (ε * Real.sqrt (Real.log (N : ℝ))) * Real.sqrt (Real.log (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right h1 hsqrt_nn
    have h3 : (ε * Real.sqrt (Real.log (N : ℝ))) * Real.sqrt (Real.log (N : ℝ))
              = ε * Real.log (N : ℝ) := by
      have hss : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ))
              = Real.log (N : ℝ) := by
        have h := hsq_sqrt
        rw [sq] at h
        exact h
      calc (ε * Real.sqrt (Real.log (N : ℝ))) * Real.sqrt (Real.log (N : ℝ))
          = ε * (Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ))) := by ring
        _ = ε * Real.log (N : ℝ) := by rw [hss]
    linarith [h2, h3.le, h3.ge]
  -- Therefore -ε * log N ≤ -4 * sqrt(log N).
  have hneg_ineq : -(ε * Real.log (N : ℝ)) ≤ -4 * Real.sqrt (Real.log (N : ℝ)) := by
    linarith
  -- So exp(-ε log N) ≤ exp(-4 sqrt(log N)).
  have hexp_ineq : Real.exp (-(ε * Real.log (N : ℝ))) ≤
                    Real.exp (-4 * Real.sqrt (Real.log (N : ℝ))) := by
    exact Real.exp_le_exp.mpr hneg_ineq
  -- N^(-ε) = exp(-ε * log N).
  have hNpos : (0 : ℝ) < (N : ℝ) := hN0R
  have hrpow_neg : (N : ℝ) ^ (-ε) = Real.exp (-(ε * Real.log (N : ℝ))) := by
    rw [Real.rpow_def_of_pos hNpos]
    ring_nf
  -- So N^(-ε) ≤ exp(-4 sqrt(log N)).
  have hkey : (N : ℝ) ^ (-ε) ≤ Real.exp (-4 * Real.sqrt (Real.log (N : ℝ))) := by
    rw [hrpow_neg]
    exact hexp_ineq
  -- N * N^(-ε) ≤ N * exp(-4 sqrt(log N)).
  have hmul : (N : ℝ) * (N : ℝ) ^ (-ε) ≤
              (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (N : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hkey (le_of_lt hN0R)
  -- N * N^(-ε) = N^(1-ε).
  have hN_rpow1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
  have hN_split : (N : ℝ) ^ (1 - ε) = (N : ℝ) * (N : ℝ) ^ (-ε) := by
    have h : (N : ℝ) ^ (1 + (-ε)) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-ε) :=
      Real.rpow_add hNpos 1 (-ε)
    have h' : (1 : ℝ) + (-ε) = 1 - ε := by ring
    rw [h'] at h
    rw [h, ← hN_rpow1]
  -- Therefore N^(1-ε) ≤ N * exp(-4 sqrt(log N)).
  have hN_le_exp : (N : ℝ) ^ (1 - ε) ≤
      (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (N : ℝ))) := by
    rw [hN_split]; exact hmul
  -- Behrend: N * exp(-4 sqrt(log N)) ≤ rothNumberNat N.
  have hBehrend : (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (N : ℝ))) ≤
                   (rothNumberNat N : ℝ) := Behrend.roth_lower_bound
  -- Combine.
  have hN_le_roth : (N : ℝ) ^ (1 - ε) ≤ (rothNumberNat N : ℝ) :=
    le_trans hN_le_exp hBehrend
  -- Extract witness.
  obtain ⟨S, hS_sub, hS_card, hS_3AP⟩ := rothNumberNat_spec N
  refine ⟨S, hS_sub, hS_3AP, ?_⟩
  rw [hS_card]
  exact hN_le_roth
