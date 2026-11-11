-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_3_2
-- name    : ArbLindbladLearn.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:28:10.176568+00:00
-- url     : https://prove2.me/theorems/9213adc7-565b-4fa3-b09f-638d95e5bf42
-- title:
--   Lemma 3.2 — effective sparsity
-- statement:
--   Let $\mathcal L$ be an $n$-qubit Lindbladian with $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$ and $\chi$-matrix $\mathcal L(\rho)=\sum_{a,b}\chi_{ab}P_a\rho P_b$ (eq. (13)). Then
--   $$2\sum_{a\ne0}|h_a|^2+\sum_{a,b\ne0}|\gamma_{ab}|^2\le\sum_{a,b}|\chi_{ab}|^2\le\Lambda^2\quad(14).$$
--   Consequently, for every $\eta>0$, with $\mathcal S_H^{\ge\eta}=\{a\ne0:|h_a|\ge\eta\}$ and $\mathcal S_D^{\ge\eta}=\{(a,b):a,b\ne0,|\gamma_{ab}|\ge\eta\}$,
--   $$2|\mathcal S_H^{\ge\eta}|+|\mathcal S_D^{\ge\eta}|\le\frac{\Lambda^2}{\eta^2}\quad(15).$$
--
--   The dynamical strength alone bounds the number of heavy coefficients, which gives the sparsity clause $9\Lambda^2/\varepsilon^2$ of Corollary 4.7.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ (induced spectral norm, Hilbert–Schmidt adjoint) → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.2, eqs. (14)–(15), p.18; Definition 2.7, p.14

import Mathlib
import Definitions.Def_ArbLindbladLearn_chiCoeff
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

open Classical in
/-- Lemma 3.2 (Effective sparsity; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), eqs. (14)–(15), p.18). Let `ℒ` be
an `n`-qubit Lindbladian with `‖ℒ†‖_{∞→∞} ≤ Λ` and `χ`-matrix as in eq. (13). Then
`2 Σ_{a≠0} |h_a|² + Σ_{a,b≠0} |γ_ab|² ≤ Σ_{a,b} |χ_ab|² ≤ Λ²` (14). Consequently, for every `η > 0`,
`2|𝒮_H^{≥η}| + |𝒮_D^{≥η}| ≤ Λ²/η²` (15).

**Formalization Note** The standing assumption `‖ℒ†‖_{∞→∞} ≤ Λ` (p.14) is `StrengthLE c Λ`; `IsLindbladCoeffs c` says
the Kossakowski matrix is Hermitian PSD (Definition 2.6). `χ_ab = chiCoeff (gen c) a b` over all labels including `0`.
`𝒮_H^{≥η} = {a ≠ 0 : |h_a| ≥ η}` and `𝒮_D^{≥η} = {(a, b) : a, b ≠ 0, |γ_ab| ≥ η}` (Definition 2.7,
p.14). -/
theorem lemma_3_2 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) (Λ : ℝ)
    (hΛ : StrengthLE c Λ) :
    (2 * ∑ a ∈ Finset.univ.filter (fun a : Pauli n => a ≠ 0), |c.h a| ^ 2 +
        ∑ a ∈ Finset.univ.filter (fun a : Pauli n => a ≠ 0),
          ∑ b ∈ Finset.univ.filter (fun b : Pauli n => b ≠ 0), ‖c.γ a b‖ ^ 2 ≤
      ∑ a : Pauli n, ∑ b : Pauli n, ‖chiCoeff (gen c) a b‖ ^ 2 ∧
    ∑ a : Pauli n, ∑ b : Pauli n, ‖chiCoeff (gen c) a b‖ ^ 2 ≤ Λ ^ 2) ∧
    ∀ η : ℝ, 0 < η →
      2 * ((Finset.univ.filter (fun a : Pauli n => a ≠ 0 ∧ η ≤ |c.h a|)).card : ℝ) +
        ((Finset.univ.filter (fun p : Pauli n × Pauli n =>
          p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ η ≤ ‖c.γ p.1 p.2‖)).card : ℝ) ≤ Λ ^ 2 / η ^ 2 := by sorry

end ArbLindbladLearn
