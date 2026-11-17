-- Prove2me | solution 1 for thm_8_7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:29:15.789207+00:00
-- url     : https://prove2.me/submissions/d9c9d413-0d05-473d-8887-19298d3e060b

import Definitions.Def_ProbabilityTheory_chapter_08_def_8_1_F000
import Definitions.Def_ProbabilityTheory_chapter_08_def_8_5_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic


/-

  # Theorem 8.8   Coupling inequality

-/

/-
\begin{thmbox}{8.7 (Coupling Inequality)}
Given two probability measures $P$ and $Q$ defined on the same measurable space $(\mathcal{X},\mathcal{F})$, any coupling of $(X,Y)$ defined on a probability space $(\Omega,\mathcal{H},\mu)$ satisfies
\[
d_{TV}(P,Q)\le \mu(\{X\neq Y\}).
\]
\end{thmbox}

\textit{Proof} The proof depends on the following trick. For any subset $A\subseteq \mathcal{X}$ that is $\mathcal{F}$-measurable, we have
\[
P(A)-Q(A)=\mu(X\in A)-\mu(Y\in A)
\]
\[
=\mu(X\in A, X=Y)+\mu(X\in A, X\neq Y)
\]
\[
\qquad -\mu(Y\in A, X=Y)-\mu(Y\in A, X\neq Y)
\]
\[
=\mu(X\in A, X\neq Y)-\mu(Y\in A, X\neq Y)
\]
\[
\le \mu(X\in A, X\neq Y).
\]

Taking supremum over all $A\in \mathcal{F}$ on both sides, we get
\[
\sup_{A\in \mathcal{F}} (P(A)-Q(A))
\le
\sup_{A\in \mathcal{F}} \mu(X\in A, X\neq Y).
\]

The last supremum is achieved when $A=\mathcal{X}$. This proves $d_{TV}(P,Q)\le \mu(X\neq Y)$. \hfill $\square$
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set --ProbabilityTheory Set

noncomputable section


private theorem coupling_abs_bound_of_measurable
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) (A : Set α) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ π.μ.real {ω : π.Ω | π.X ω ≠ π.Y ω} := by
  let mismatch : Set π.Ω := {ω : π.Ω | π.X ω ≠ π.Y ω}
  have hP : P.real A = π.μ.real (π.X ⁻¹' A) := by
    simpa [π.map_X] using
      (MeasureTheory.map_measureReal_apply (μ := π.μ) π.measurable_X hA)
  have hQ : Q.real A = π.μ.real (π.Y ⁻¹' A) := by
    simpa [π.map_Y] using
      (MeasureTheory.map_measureReal_apply (μ := π.μ) π.measurable_Y hA)
  have hsubXY : π.X ⁻¹' A ⊆ π.Y ⁻¹' A ∪ mismatch := by
    intro ω hω
    by_cases hEq : π.X ω = π.Y ω
    · left
      simpa [Set.mem_preimage, hEq] using hω
    · right
      simp [mismatch, hEq]
  have hsubYX : π.Y ⁻¹' A ⊆ π.X ⁻¹' A ∪ mismatch := by
    intro ω hω
    by_cases hEq : π.X ω = π.Y ω
    · left
      simpa [Set.mem_preimage, hEq] using hω
    · right
      simp [mismatch, hEq]
  have hXY_le :
      π.μ.real (π.X ⁻¹' A) ≤ π.μ.real (π.Y ⁻¹' A) + π.μ.real mismatch := by
    refine le_trans (MeasureTheory.measureReal_mono hsubXY) ?_
    exact MeasureTheory.measureReal_union_le (π.Y ⁻¹' A) mismatch
  have hYX_le :
      π.μ.real (π.Y ⁻¹' A) ≤ π.μ.real (π.X ⁻¹' A) + π.μ.real mismatch := by
    refine le_trans (MeasureTheory.measureReal_mono hsubYX) ?_
    exact MeasureTheory.measureReal_union_le (π.X ⁻¹' A) mismatch
  have h1 : π.μ.real (π.X ⁻¹' A) - π.μ.real (π.Y ⁻¹' A) ≤ π.μ.real mismatch := by
    linarith
  have h2 : π.μ.real (π.Y ⁻¹' A) - π.μ.real (π.X ⁻¹' A) ≤ π.μ.real mismatch := by
    linarith
  change |P.real A - Q.real A| ≤ π.μ.real mismatch
  rw [hP, hQ]
  exact (abs_sub_le_iff.2 ⟨h1, h2⟩)

theorem solution
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) :
    totalVariationDistance P Q ≤ π.μ.real {ω : π.Ω | π.X ω ≠ π.Y ω} := by
  let mismatch : Set π.Ω := {ω : π.Ω | π.X ω ≠ π.Y ω}
  let S : Set ℝ := {d : ℝ | ∃ A : Set α, MeasurableSet A ∧ d = |P.real A - Q.real A|}
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simp
  have hbound : ∀ d ∈ S, d ≤ π.μ.real mismatch := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    exact coupling_abs_bound_of_measurable π A hA
  unfold totalVariationDistance
  change sSup S ≤ π.μ.real mismatch
  exact csSup_le hnonempty hbound