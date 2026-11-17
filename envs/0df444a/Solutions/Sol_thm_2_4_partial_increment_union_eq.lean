-- Prove2me | solution 1 for thm_2_4_partial_increment_union_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:31:56.56235+00:00
-- url     : https://prove2.me/submissions/69fe9564-b438-4ed1-ae1d-a1c925bf6434

import Theorems.Thm_thm_2_4_increment_subset
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic


/-

 Theorem 2.4 Lower semi-continuity of measure

-/

/-
\begin{thmbox}{2.4 (Lower Semi-Continuity)}
Suppose $A_1\subseteq A_2\subseteq A_3\subseteq \cdots$ is a sequence of increasing sets in $\mathcal{F}$ and $(\Omega,\mathcal{F},\mu)$ is a measure space. Then
\[
\lim_{k\to\infty} \mu(A_k)=\mu\left(\bigcup_{i=1}^{\infty} A_i\right).
\]
\end{thmbox}

\textit{Proof} Let $B_1=A_1$ and $B_i=A_i\setminus A_{i-1}$ for $i\ge 2$. The sets $B_i$'s are mutually disjoint by construction. Moreover, we have $\biguplus_{i=1}^{\infty} B_i=\cup_{i=1}^{\infty} A_i$. This gives
\[
\lim_{k\to\infty} \mu(A_k)
=
\lim_{k\to\infty} \mu(B_1 \uplus B_2 \uplus \cdots \uplus B_k)
\]
\[
=
\lim_{k\to\infty} \sum_{i=1}^{k} \mu(B_i)
\triangleq
\sum_{i=1}^{\infty} \mu(B_i)
=
\mu\left(\biguplus_{i=1}^{\infty} B_i\right)
=
\mu\left(\bigcup_{i=1}^{\infty} A_i\right),
\]
where the second last equality follows from the countable additivity of measure $\mu$. \hfill $\square$
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators

/-- Each increment is contained in the corresponding increasing-set term. -/
private theorem partial_increment_union_subset
    {Ω : Type*} {A : ℕ → Set Ω} (hA : SetSeqIncreasing A) (n : ℕ) :
    (⋃ i ∈ Set.Iic n, thm_2_4_increment A i) ⊆ A n := by
  change Monotone A at hA
  intro x hx
  rcases mem_iUnion.mp hx with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨hi_le, hxB⟩
  exact hA hi_le (thm_2_4_increment_subset A i hxB)

/-- Every point of the increasing-set term lies in some increment up to n. -/
private theorem partial_increment_union_superset
    {Ω : Type*} {A : ℕ → Set Ω} (hA : SetSeqIncreasing A) (n : ℕ) :
    A n ⊆ (⋃ i ∈ Set.Iic n, thm_2_4_increment A i) := by
  change Monotone A at hA
  induction n with
  | zero =>
      intro x hx
      refine mem_iUnion.mpr ⟨0, ?_⟩
      exact mem_iUnion.mpr
        ⟨(by simp : 0 ∈ Set.Iic 0), by simpa [thm_2_4_increment] using hx⟩
  | succ n ih =>
      intro x hx
      by_cases hxAn : x ∈ A n
      · have hx_partial_n := ih hxAn
        rcases mem_iUnion.mp hx_partial_n with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨hi_le, hxB⟩
        refine mem_iUnion.mpr ⟨i, ?_⟩
        have hi_le_nat : i ≤ n := by simpa using hi_le
        exact mem_iUnion.mpr
          ⟨(by simpa using Nat.le_trans hi_le_nat (Nat.le_succ n)), hxB⟩
      · refine mem_iUnion.mpr ⟨n + 1, ?_⟩
        exact mem_iUnion.mpr
          ⟨(by simp : n + 1 ∈ Set.Iic (n + 1)), by exact ⟨hx, hxAn⟩⟩

theorem solution {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    ∀ n : ℕ, (⋃ i ∈ Set.Iic n, thm_2_4_increment A i) = A n := by
  intro n
  exact Set.Subset.antisymm
    (partial_increment_union_subset hA n)
    (partial_increment_union_superset hA n)
