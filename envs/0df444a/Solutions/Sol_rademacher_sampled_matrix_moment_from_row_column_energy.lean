-- Prove2me | solution 1 for rademacher_sampled_matrix_moment_from_row_column_energy
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T14:39:47.72904+00:00
-- url     : https://prove2.me/submissions/e17c3f4a-4005-4785-9d5b-d2ce7bb13c21

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_conditional_khintchine_scale_moment_from_row_column_energy_moment
import Theorems.Thm_rademacher_sampled_matrix_conditional_khintchine_bound
import Theorems.Thm_bernoulli_expectation_monotone
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

/-- The averaged-over-Ω operator-norm moment bound follows by chaining:
(1) the per-Ω conditional Khintchine bound
`rademacher_sampled_matrix_conditional_khintchine_bound`, giving the Rademacher
inner expectation a pointwise (in Ω) bound by `(Ckh√q p⁻¹√Z)^q`;
(2) Bernoulli monotonicity over Ω; and
(3) the conditional-Khintchine *scale* moment bound
`conditional_khintchine_scale_moment_from_row_column_energy_moment`, which turns
the row/column energy moment hypothesis into the final
`(Crad√(qn/p)‖X‖_∞)^q` bound. -/
theorem solution
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCe
  -- per-Ω conditional Khintchine constant
  obtain ⟨Ckh, hCkh, hkh⟩ :=
    rademacher_sampled_matrix_conditional_khintchine_bound
  -- scale-moment reduction constant (consumes Cenergy + Ckh)
  obtain ⟨Crad, hCrad, hscale⟩ :=
    conditional_khintchine_scale_moment_from_row_column_energy_moment Cenergy Ckh hCe hCkh
  refine ⟨Crad, hCrad, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hmlb hq1 hqlb hqub hqp hH
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- p ∈ [0,1]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by positivity)]
    calc (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
      _ = (n₁ : ℝ) * (n₂ : ℝ) := by push_cast; ring
  -- Step 1 (per Ω): E_ε[‖R‖_op^q] ≤ (Ckh√q p⁻¹ √Z)^q
  have hpt : ∀ Ω : Finset (Fin n₁ × Fin n₂),
      rademacherExpectation
          (fun eps => spectralNorm (rademacherSampledMatrix Ω eps p X) ^ q)
        ≤ (Ckh * Real.sqrt (q:ℝ) * p⁻¹ *
            Real.sqrt (max (sampledRowEnergyMax Ω X)
              (sampledColumnEnergyMax Ω X))) ^ q := by
    intro Ω
    have := hkh β hβ n₁ n₂ m q Ω X hq1 hqlb
    rw [hp]; exact this
  -- Step 2: Bernoulli monotonicity over Ω
  have hmono :
      bernoulliExpectation p
          (fun Ω => rademacherExpectation
            (fun eps => spectralNorm (rademacherSampledMatrix Ω eps p X) ^ q))
        ≤ bernoulliExpectation p
          (fun Ω => (Ckh * Real.sqrt (q:ℝ) * p⁻¹ *
            Real.sqrt (max (sampledRowEnergyMax Ω X)
              (sampledColumnEnergyMax Ω X))) ^ q) :=
    bernoulli_expectation_monotone p _ _ hp0 hp1 hpt
  -- Step 3: scale-moment reduction
  have hsc := hscale β hβ n₁ n₂ m q X hn₁ hn₂ hm hmlb hq1 hqlb hqub hqp
  -- rewrite p back into hH/hsc forms
  rw [hp]
  rw [hp] at hmono
  refine le_trans hmono ?_
  exact hsc hH
