-- Prove2me | Theorems.Thm_BosonicLearn_measure_of_uniform_limit
-- name    : BosonicLearn.measure_of_uniform_limit
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:02:55.678205+00:00
-- url     : https://prove2.me/theorems/f5f9369b-3f32-452f-8244-db394e4adbff
-- title:
--   A uniform limit of finite measures is a finite measure
-- statement:
--   A set function that is uniformly approximated by finite measures is a finite measure.
--
--   Let $(X,\mathcal A)$ be a measurable space, $\beta$ a real-valued function on the subsets of $X$, $\lambda_0,\lambda_1,\dots$ finite measures on $X$ and $\varepsilon_0,\varepsilon_1,\dots$ real numbers with $\varepsilon_n\to0$ and
--
--   $$
--   |\beta(C)-\lambda_n(C)|\le\varepsilon_n\qquad\text{for every } n\text{ and every } C\in\mathcal A .
--   $$
--
--   Then there is a finite measure $\mu$ on $X$ with $\mu(C)=\beta(C)$ for every $C\in\mathcal A$.
--
--   Role. For a POVM with effects $E(C)$ on an infinite-dimensional space and a density operator $\rho$, the set function $C\mapsto\operatorname{Re}\operatorname{Tr}(E(C)\rho)$ is the uniform limit of the measures $C\mapsto\operatorname{Tr}(E(C)\rho_F)$ of the finite truncations $\rho_F$ of $\rho$, with error at most $\|\rho-\rho_F\|_1$ for every $C$. This lemma turns it into a measure, which is the outcome law required of a `FockPOVM`. It is used in the construction of the sequential composition of two POVMs (`BosonicLearn.fockPOVM_compose`).
--
--   **Formalization Note** The conclusion is $\mu(C)=$ `ENNReal.ofReal (β C)` on measurable sets; the hypotheses force $\beta(C)\ge0$ there. Values of $\beta$ on non-measurable sets are irrelevant. The statement is pure measure theory and uses no definition of the mission.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 (general POVM measurements with continuous outcomes); auxiliary measure-theoretic lemma for the proof of Theorem 3, p. 67

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace BosonicLearn

/-- **A uniform limit of finite measures is a finite measure.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "All of our theorems stated in Sec. 1.2 hold for general POVM measurements on n-mode
bosonic systems"; the outcome distribution of a POVM on a state `ρ` is the measure `B ↦ Tr(E(B) ρ)`.

Let `β` be a real-valued function on the subsets of a measurable space `X`, let `λ₀, λ₁, …` be finite measures
on `X` and let `ε₀, ε₁, … → 0` be real numbers with `|β(C) − λₙ(C)| ≤ εₙ` for every `n` and every measurable
`C`. Then there is a finite measure `μ` on `X` with `μ(C) = β(C)` for every measurable `C`.

**Formalization Note.** `μ(C) = ENNReal.ofReal (β C)`; the hypotheses force `β(C) ≥ 0` on measurable sets. This
is the tool that turns the set function `C ↦ Re Tr(E(C) ρ)` of an infinite-dimensional density operator `ρ` into
a measure: it is a uniform limit of the measures obtained from finite truncations of `ρ`. -/
theorem measure_of_uniform_limit {X : Type} [MeasurableSpace X] (β : Set X → ℝ) (lam : ℕ → Measure X)
    (hfin : ∀ n, IsFiniteMeasure (lam n)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ n C, MeasurableSet C → |β C - (lam n C).toReal| ≤ ε n) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ C, MeasurableSet C → μ C = ENNReal.ofReal (β C) := by sorry

end BosonicLearn
