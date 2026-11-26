-- Prove2me | Theorems.Thm_DiagonalizationGeneral
-- name    : DiagonalizationGeneral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:19.605251+00:00
-- url     : https://prove2.me/theorems/780b66c4-8721-5905-a680-e06f1e171657
-- title:
--   Diagonalization General: Diagonalization General
-- statement:
--   Paper.tex 1382-1435 (eq. diagonalization_general), the upgrade of the current identity from
--   the countable dense family `om` supplied by `\noderef{LipschitzSeparable}` (Lemma A.1) to *every*
--   metric `1`-form `ω`. Given a metric `1`-current `T` with a Paolini-Stepanov family `F` and a
--   countable dense set `D`, there is a countable family `om : ℕ → Form1 E` such that: whenever `n`,
--   `γ` witness `\noderef{BBSamplingDiagonal}`'s conclusion restricted to `om` (the current-average
--   clause at every `om k`, and the `ψ`/`ψ̃`-average clause at every admissible `(m,Q,ε,C)` with
--   `Q ⊆ D`), the current-average identity in fact holds at *every* `1`-form `ω`, not just at the
--   members of `om`. This is the missing step that lets `\noderef{ClosingUp}`'s hypothesis (H2) be
--   discharged for a general `ω`, as required by target `bbassertion`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/DiagonalizationGeneral.lean#L28-L265
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/DiagonalizationGeneral.lean#L28-L265

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_LipschitzSeparable
import Definitions.Def_Tablet_CurrentFormAddF
import Definitions.Def_Tablet_CurrentTwoFormEstimate
import Definitions.Def_Tablet_CurrentFormAddPi
import Definitions.Def_Tablet_PiBoundsF
import Definitions.Def_Tablet_PiBoundsPi
import Definitions.Def_Tablet_PsiVanishes
import Definitions.Def_Tablet_CurrentContinuousF
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_DiagonalizationGeneral
import Theorems.Thm_CurrentContinuousF
import Theorems.Thm_CurrentFormAddF
import Theorems.Thm_CurrentFormAddPi
import Theorems.Thm_CurrentTwoFormEstimate
import Theorems.Thm_LipschitzSeparable
import Theorems.Thm_PiBoundsF
import Theorems.Thm_PiBoundsPi
import Theorems.Thm_PsiVanishes

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open scoped NNReal

theorem DiagonalizationGeneral {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (T : MetricCurrent1 E) (F : PSFamily T.toFun)
    (D : Set E) (hDc : D.Countable) (hDne : D.Nonempty) (hDd : Dense D) :
    ∃ om : ℕ → Form1 E,
      ∀ (n : ℕ → ℕ) (γ : ℕ → ℕ → Curve E),
        (∀ l : ℕ, 0 < n l) →
        (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (γ l i).len = (l : ℝ)) →
        (∀ k : ℕ, Tendsto (fun l : ℕ =>
            (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (om k))
            atTop (nhds (T.toFun (om k)))) →
        (∀ m : ℕ, 1 ≤ m → ∀ Q : Finset E, Q.Nonempty → (Q : Set E) ⊆ D →
          ∀ ε C : ℚ, 0 < ε → 0 < C →
            Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psi (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
              atTop (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
                ∫ c, psi m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))
            ∧ Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psiTilde (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
              atTop (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
                ∫ c, psiTilde m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))) →
        ∀ ω : Form1 E, Tendsto (fun l : ℕ =>
            (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
            atTop (nhds (T.toFun ω)) := by sorry
