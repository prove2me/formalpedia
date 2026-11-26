-- Prove2me | Theorems.Thm_BBSamplingDiagonal
-- name    : BBSamplingDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:57.047459+00:00
-- url     : https://prove2.me/theorems/c57ec5a6-5d72-4c92-b22f-5333a4f08a28
-- title:
--   BBSampling Diagonal: BBSampling Diagonal
-- statement:
--   The single remaining diagonal extraction of Theorem 4.4's proof (paper.tex 1349-1360,
--   \eqref{diag_T} and its companions), stated at the level of the *unsampled* curves `γ_{i,l}` per
--   restructuring (B) (`\noderef{GeodesicSampledCurrent}` transfers the piecewise-geodesic sampling
--   error separately, once, downstream in `\noderef{ClosingUp}`; it never enters this node). Given a
--   Paolini–Stepanov family `F` for `T` with nonzero mass measure, a countable family `om` of `1`-forms,
--   a basepoint `x0`, and a countable dense set `D` (supplying the admissible test sets `Q`), there is
--   a single sequence of positive integers `n l → ∞` and a doubly-indexed family of curves `γ l i`
--   (`l ∈ ℕ`, `i < n l`) of length exactly `l` and current-mass exactly `l`, along which *all three*
--   `l`-independent countable families of stage-wise strong-law limits converge simultaneously: the
--   current averages against `om` (converging to `T`, carrying the explicit `F.massMeasure Set.univ`
--   normalizing factor of eq.~(4.6)), the endpoint-cutoff mass-marginal averages at every positive
--   rational radius `r` (converging to the normalized `F.massMeasure`-mass of the complement of the
--   `r`-ball at `x0`), and the `ψ`/`ψ̃`-averages at every admissible `(m,Q,ε,C)` (converging to the
--   `F.eta 1`-average, via `\noderef{EtaRepeats}`/`\noderef{EtaRepeatsTilde}`'s `l`-independence).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BBSamplingDiagonal.lean#L30-L478
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BBSamplingDiagonal.lean#L30-L478

import Definitions.Def_Tablet_SLLNCurves
import Definitions.Def_Tablet_CountableDiagonalExtraction
import Definitions.Def_Tablet_EtaRepeats
import Definitions.Def_Tablet_EtaRepeatsTilde
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Definitions.Def_Tablet_PsiUniformBound
import Definitions.Def_Tablet_PsiTildeUniformBound
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_BBSamplingDiagonal
import Theorems.Thm_CountableDiagonalExtraction
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_EtaRepeats
import Theorems.Thm_EtaRepeatsTilde
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiTildeMeasurable
import Theorems.Thm_PsiTildeUniformBound
import Theorems.Thm_PsiUniformBound
import Theorems.Thm_SLLNCurves

set_option autoImplicit false
open MeasureTheory Filter Finset ENNReal

theorem BBSamplingDiagonal {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T) (hT0 : F.massMeasure Set.univ ≠ 0)
    (om : ℕ → Form1 E) (x0 : E)
    (D : Set E) (hDc : D.Countable) (hDne : D.Nonempty) (hDd : Dense D) :
    ∃ n : ℕ → ℕ, (∀ l : ℕ, 0 < n l) ∧ Tendsto n atTop atTop ∧
    ∃ γ : ℕ → ℕ → Curve E,
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (γ l i).len = (l : ℝ)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, massOfFunctional (curveCurrent (γ l i)) = (l : ℝ≥0∞)) ∧
      (∀ k : ℕ, Tendsto (fun l : ℕ =>
          (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (om k))
          atTop (nhds (T (om k)))) ∧
      (∀ r : ℚ, 0 < r →
        Tendsto (fun l : ℕ =>
            (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
              (if (r : ℝ) ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0))
          atTop
          (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
            (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal))
        ∧
        Tendsto (fun l : ℕ =>
            (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
              (if (r : ℝ) ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0))
          atTop
          (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
            (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal))) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ Q : Finset E, Q.Nonempty → (Q : Set E) ⊆ D →
        ∀ ε C : ℚ, 0 < ε → 0 < C →
          Tendsto (fun l : ℕ =>
              (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psi (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
            atTop
            (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
              ∫ c, psi m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))
          ∧
          Tendsto (fun l : ℕ =>
              (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psiTilde (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
            atTop
            (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
              ∫ c, psiTilde m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))) := by sorry
