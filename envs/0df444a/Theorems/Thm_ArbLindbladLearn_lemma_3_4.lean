-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_3_4
-- name    : ArbLindbladLearn.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:28:25.619047+00:00
-- url     : https://prove2.me/theorems/be8624e2-7b1f-4937-bfd3-34ea4578b538
-- title:
--   Lemma 3.4 — derivative bound for Choi matrix elements
-- statement:
--   Let $\mathcal L$ be a Lindbladian with dynamical strength at most $\Lambda$. For operators $A,B$ define $f_{A,B}(t)=\langle\Phi_A|J_t|\Phi_B\rangle$. Then for every $r\in\mathbb N$ and $t\ge0$,
--   $$\big|f^{(r)}_{A,B}(t)\big|\le\|A\|_\infty\|B\|_\infty\Lambda^r .$$
--
--   This uniform bound on all time derivatives is what makes Chebyshev endpoint interpolation accurate, both for support learning and coefficient learning.
--
--   Differences from the source:
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ (induced spectral norm, Hilbert–Schmidt adjoint) → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - encoding: f^{(r)}_{A,B}(t) for t ≥ 0 (one-sided at t = 0) → iteratedDeriv r (two-sided) at t ≥ 0; reason: f_{A,B} is entire in t, so the derivatives agree
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.4, p.20

import Mathlib
import Definitions.Def_ArbLindbladLearn_signal
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Lemma 3.4 (Derivative bound for Choi matrix elements; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.20). Let
`ℒ` be a Lindbladian with dynamical strength at most `Λ`. For `A, B ∈ ℬ(ℋ)` and
`f_{A,B}(t) = ⟨Φ_A|J_t|Φ_B⟩`, for every `r ∈ ℕ` and `t ≥ 0`,
`|f^{(r)}_{A,B}(t)| ≤ ‖A‖_∞ ‖B‖_∞ Λʳ`.

**Formalization Note** The standing assumption `‖ℒ†‖_{∞→∞} ≤ Λ` (p.14) is `StrengthLE c Λ`; `IsLindbladCoeffs c` says
the Kossakowski matrix is Hermitian PSD (Definition 2.6). `‖·‖_∞` is the spectral norm `opNorm`; `r = 0` is included. -/
theorem lemma_3_4 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) (Λ : ℝ)
    (hΛ : StrengthLE c Λ) (A B : Op (Qubits n)) (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖iteratedDeriv r (fun s => signal c A B s) t‖ ≤ opNorm A * opNorm B * Λ ^ r := by sorry

end ArbLindbladLearn
