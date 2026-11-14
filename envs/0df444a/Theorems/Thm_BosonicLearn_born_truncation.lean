-- Prove2me | Theorems.Thm_BosonicLearn_born_truncation
-- name    : BosonicLearn.born_truncation
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:08:21.870385+00:00
-- url     : https://prove2.me/theorems/9bb31190-db02-4e18-970f-7ebd0465345e
-- title:
--   Born probabilities $\mathrm{Tr}(E\rho)$ are approximated by finite blocks of $\rho$, uniformly over all effects $E$
-- statement:
--   The Born probabilities of an infinite-dimensional density operator are approximated by those of its finite blocks, with an error that is uniform over all effects.
--
--   Let $I$ be an index set and $X$ a density operator on $\ell^2(I)$ (trace class, positive semidefinite, trace one). An effect is a coefficient array $E=(E_{ij})_{i,j\in I}$ with $0\le\langle z,Ez\rangle\le\langle z,z\rangle$ for every finitely supported vector $z$. Write
--
--   $$
--   \operatorname{Tr}(EX)=\sum_{i}\sum_{j}E_{ij}X_{ji},\qquad \operatorname{Tr}_F(EX)=\sum_{i\in F}\sum_{j\in F}E_{ij}X_{ji}\quad\text{for finite }F\subseteq I .
--   $$
--
--   Then:
--
--   1. For every $\eta>0$ there is a finite $F_0\subseteq I$ such that for every finite $F\supseteq F_0$ and every effect $E$,
--   $$
--   \big|\operatorname{Tr}(EX)-\operatorname{Tr}_F(EX)\big|\le\eta .
--   $$
--   2. For every finite $F$ and every effect $E$, $\operatorname{Tr}_F(EX)$ is real and non-negative.
--   3. For every effect $E$, $\operatorname{Tr}(EX)$ is real and non-negative.
--
--   Role. Item 1 is the quantitative form of $|\operatorname{Tr}(E(\rho-\rho_F))|\le\|\rho-\rho_F\|_1$ for the truncation $\rho_F$ of $\rho$ to the block $F\times F$, with $\|\rho-\rho_F\|_1\to0$. Because $F_0$ does not depend on $E$, the outcome law $C\mapsto\operatorname{Tr}(E(C)X)$ of a POVM is a uniform limit of finite-dimensional ones. This is used to build Born laws of POVMs on infinite-dimensional systems (`BosonicLearn.fockPOVM_compose`), together with `BosonicLearn.measure_of_uniform_limit`.
--
--   **Formalization Note** The effect condition is the hypothesis `effect_form` of `FockPOVM`, on finite sets $s$ and coefficient functions $z$: the form $\sum_{i,j\in s}\overline{z_i}E_{ij}z_j$ has imaginary part $0$ and real part in $[0,\sum_{i\in s}|z_i|^2]$. $\operatorname{Tr}(EX)$ is the iterated unconditional series `∑' i, ∑' j, E i j * X j i`, the form in which `FockPOVM.law_born` states the Born rule. Density and trace class are `IsDensity` (nuclear-expansion sense).
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators). The proof imports `BosonicLearn.effect_matrix_operator` and `BosonicLearn.effect_trace_pairing`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 (general POVM measurements); Eq. (105), p. 40 (trace-distance bound on outcome probabilities); auxiliary lemma for Theorem 3, p. 67

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Born probabilities are approximated by finite truncations, uniformly over all effects.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5 (general POVM measurements; outcome probabilities `Tr(E ρ)`), and Eq. (105), p. 40
(`|Tr(E(ρ − σ))| ≤ ‖ρ − σ‖₁` for `0 ≤ E ≤ I`).

Let `X` be a density operator on `ℓ²(I)`. Call `E` an *effect* if `0 ≤ ⟨z, E z⟩ ≤ ⟨z, z⟩` (real) for every finitely
supported `z`, and write `Tr(E X) = ∑ᵢ ∑ⱼ E_ij X_ji` and `Tr_F(E X) = ∑_{i,j ∈ F} E_ij X_ji` for finite `F ⊆ I`.

1. For every `η > 0` there is a finite `F₀ ⊆ I` such that `|Tr(E X) − Tr_F(E X)| ≤ η` for **every** finite
   `F ⊇ F₀` and **every** effect `E`.
2. For every finite `F` and every effect `E`, `Tr_F(E X)` is real and non-negative.
3. For every effect `E`, `Tr(E X)` is real and non-negative.

**Formalization Note.** Effects are coefficient arrays with the bounds of `FockPOVM.effect_form`; density and
trace class are `IsDensity`. The set `F₀` in (1) depends on `X` and `η` only. -/
theorem born_truncation {I : Type} [DecidableEq I] (X : Matrix I I ℂ) (hX : IsDensity X) :
    (∀ η : ℝ, 0 < η → ∃ F₀ : Finset I, ∀ F : Finset I, F₀ ⊆ F → ∀ E : Matrix I I ℂ,
      (∀ (s : Finset I) (z : I → ℂ),
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
        0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) →
      ‖(∑' i, ∑' j, E i j * X j i) - ∑ i ∈ F, ∑ j ∈ F, E i j * X j i‖ ≤ η) ∧
    (∀ (F : Finset I) (E : Matrix I I ℂ),
      (∀ (s : Finset I) (z : I → ℂ),
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
        0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) →
      (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).im = 0 ∧ 0 ≤ (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).re) ∧
    (∀ E : Matrix I I ℂ,
      (∀ (s : Finset I) (z : I → ℂ),
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
        0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) →
      (∑' i, ∑' j, E i j * X j i).im = 0 ∧ 0 ≤ (∑' i, ∑' j, E i j * X j i).re) := by sorry

end BosonicLearn
