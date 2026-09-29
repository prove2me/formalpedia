-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T15:51:47.837766+00:00
-- url     : https://prove2.me/submissions/203bf72a-86e3-4db4-a279-10ab47c673a6

import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales

open MatrixCompletion

/-!
Source: Candes--Recht, Section 6.2, Lemma 6.6, equations (6.15)--(6.17).

This proof is the raw scalar Bernstein step at one fixed coordinate.  It keeps
the two Bernstein contributions separate: the Frobenius/variance term and the
entry-sup/range term.
-/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ w : Fin n₁ × Fin n₂,
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannOffDiagonalCoefficientBaseMatrix S w))) →
        entrySupNorm
            (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) →
        frobeniusNorm
            (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
          Cfro * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2| ≤
                Cpoint *
                  (Real.sqrt
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (Cfro * μ₁ *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Centry * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))))) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
  intro hCentry hCfro
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  refine ⟨Cbern, cbern, hCbern, hcbern, ?_⟩
  intro β lam hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower
    w hRep hEntry hFrob
  have hβshift : 2 < β + 2 := by linarith
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let entryScale : ℝ :=
    Centry * μ₁ *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))
  let frobScale : ℝ :=
    Cfro * μ₁ *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))
  have hRep' :
      ∀ Omega2 : Finset (Fin n₁ × Fin n₂),
        (fun Omega2 =>
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S p w.1 w.2)
            Omega2 =
          matrixEntrySum
            (centeredSamplingFluctuation Omega2 p
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w)) := by
    intro Omega2
    simpa [p] using hRep Omega2
  have hRaw :=
    hBernstein (β + 2) hβshift n₁ n₂ m hn₁ hn₂ hm
      (fun Omega2 =>
        linearNeumannOffDiagonalCoefficientMatrix Omega2 S p w.1 w.2)
      (linearNeumannOffDiagonalCoefficientBaseMatrix S w)
      entryScale frobScale hRep'
      (by simpa [entryScale] using hEntry)
      (by simpa [frobScale] using hFrob)
  simpa [p, entryScale, frobScale, mul_assoc] using hRaw
