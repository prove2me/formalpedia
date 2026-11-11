-- Prove2me | Theorems.Thm_ArbLindbladLearn_proof_theorem_4_6_error_propagation
-- name    : ArbLindbladLearn.proof_theorem_4_6_error_propagation
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:28:20.740901+00:00
-- url     : https://prove2.me/theorems/207c53f3-49b6-4216-ae0a-f04c17c4ee89
-- title:
--   Proof of Theorem 4.6 (pp.32–33) — node accuracy $\varepsilon/(6W)$ gives coefficient errors $2\varepsilon/3$, $\varepsilon/3$, $2\sqrt2\varepsilon/3$
-- statement:
--   Let $\mathcal L$ be a Lindbladian with $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$, $\Lambda>0$, $\varepsilon\in(0,1)$, and use Algorithm 2's parameters: $T=1/\Lambda$, $q=\min\{q'\in\mathbb N_{>0}:(q'+1)!\ge12\Lambda/\varepsilon\}$, nodes $t_j$ on $[0,T]$, $W=\sum_{j=1}^q|\ell_j'(0)|$ and $\eta_0=\varepsilon/(6W)$. Given node estimates $\hat f_A(t_j)$, let $\hat f_A'(0)=\ell_0'(0)|\mathrm{tr}A/d|^2+\sum_{j=1}^q\ell_j'(0)\hat f_A(t_j)$ and let $\hat h,\hat\gamma$ be the reconstruction of Algorithm 2 (line 25).
--   1. If $\|A\|_\infty\le\sqrt2$ and $|\hat f_A(t_j)-f_A(t_j)|\le\eta_0$ for $j=1,\dots,q$, then $|\hat f_A'(0)-f_A'(0)|\le\varepsilon/6+\varepsilon/6=\varepsilon/3$.
--   2. If the node estimates of $I,P_a,A^{\mathrm i}_{a0}$ are $\eta_0$-accurate ($a\ne0$), then $|\hat h_a-h_a|\le2\varepsilon/3$.
--   3. If those of $P_a$ are ($a\ne0$), then $|\hat\gamma_{aa}-\gamma_{aa}|\le\varepsilon/3$.
--   4. If those of $P_a,P_b,A_{ab},A^{\mathrm i}_{ab}$ are ($a,b\ne0$, $a\ne b$), then
--   $$|\hat\gamma_{ab}-\gamma_{ab}|\le\sqrt{(2\varepsilon/3)^2+(2\varepsilon/3)^2}=\frac{2\sqrt2}{3}\varepsilon .$$
--
--   This is the deterministic half of Theorem 4.6: it turns the median-of-means node guarantee into the coefficient guarantee.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ (induced spectral norm, Hilbert–Schmidt adjoint) → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - reading: T = 1/Λ (Λ > 0 implicit) → hypothesis 0 < Λ; reason: T = 1/Λ is undefined at Λ = 0
--   - generalization: every witness A ∈ 𝒲 (‖A‖_∞ ≤ √2) → every operator A with ‖A‖_∞ ≤ √2 in clause 1; reason: the proof uses only ‖A‖_∞ ≤ √2 (eq. (27)) and f_A(0) = |tr A/d|²; witnesses are instances
--   - encoding: the median-of-means node estimates f̂_A(t_j) → any reals F A j with |F A j − f_A(t_j)| ≤ η₀; reason: the step is deterministic given accurate node estimates
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), proof of Theorem 4.6, pp.32–33; Algorithm 2 lines 2–4, 23, 25, p.31

import Mathlib
import Definitions.Def_ArbLindbladLearn_derivEst
import Definitions.Def_ArbLindbladLearn_reconstruct
import Definitions.Def_ArbLindbladLearn_signal
import Definitions.Def_ArbLindbladLearn_opNorm
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Proof of Theorem 4.6, error propagation (Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), pp.32–33; Algorithm 2,
lines 2–4, 23 and 25, p.31). With `T = 1/Λ`, `q = min{q′ ∈ ℕ_{>0} : (q′+1)! ≥ 12Λ/ε}` and node
accuracy `η₀ = ε/(6W)`: if every node estimate of a witness `A` satisfies
`|f̂_A(t_j) − f_A(t_j)| ≤ η₀`, then "every witness derivative satisfies
`|f̂′_A(0) − f′_A(0)| ≤ ε/6 + ε/6 = ε/3`. By Lemma 4.2, each diagonal estimate `γ̂_aa = f̂′_{P_a}(0)`
has error at most `ε/3`. The real and imaginary parts of each off-diagonal estimate are combinations
of three derivatives whose absolute weights sum to at most 2, so each part is estimated with error
at most `2ε/3`, and `|γ̂_ab − γ_ab| ≤ √((2ε/3)² + (2ε/3)²) = (2√2/3)ε ≤ ε`. Each Hamiltonian estimate
is likewise a combination of three derivatives whose absolute weights sum to at most 2, so its
error is at most `2ε/3 ≤ ε`."

**Formalization Note** The standing assumption `‖ℒ†‖_{∞→∞} ≤ Λ` (p.14) is `StrengthLE c Λ`; `IsLindbladCoeffs c` says
the Kossakowski matrix is Hermitian PSD (Definition 2.6). `Λ > 0` is implicit in `T = 1/Λ`; `ε ∈ (0, 1)` (Theorem 4.6). The node
estimates are any reals `F A j` (`j = 1, …, q`); `f̂′_A(0)` is the line-23 rule `derivEst` and the
estimates are the line-25 reconstruction `reconstruct`. The first clause is stated for every
operator `A` with `‖A‖_∞ ≤ √2` (every witness of Definition 4.1 qualifies, p.25); each later clause
assumes accurate node estimates for exactly the witnesses its estimate reads. -/
theorem proof_theorem_4_6_error_propagation {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c)
    (Λ ε : ℝ) (hΛ : StrengthLE c Λ) (hΛ0 : 0 < Λ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (F : Op (Qubits n) → ℕ → ℝ) :
    let q := coefQ Λ ε
    let T := 1 / Λ
    let η₀ := ε / (6 * chebW q T)
    let Good : Op (Qubits n) → Prop := fun A =>
      ∀ j ∈ Finset.Icc 1 q, |F A j - witnessSignal c A (chebNode q T j)| ≤ η₀
    let D : Op (Qubits n) → ℝ := fun A => derivEst q T A (F A)
    (∀ A : Op (Qubits n), opNorm A ≤ Real.sqrt 2 → Good A →
        |D A - deriv (witnessSignal c A) 0| ≤ ε / 3) ∧
    (∀ a : Pauli n, a ≠ 0 → Good (pairWitnessI a 0) → Good (pauliMatrix a) →
        Good (pauliMatrix 0) → |(reconstruct D).h a - c.h a| ≤ 2 * ε / 3) ∧
    (∀ a : Pauli n, a ≠ 0 → Good (pauliMatrix a) →
        ‖(reconstruct D).γ a a - c.γ a a‖ ≤ ε / 3) ∧
    (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 → a ≠ b → Good (pauliMatrix a) → Good (pauliMatrix b) →
        Good (pairWitness a b) → Good (pairWitnessI a b) →
        ‖(reconstruct D).γ a b - c.γ a b‖ ≤ 2 * Real.sqrt 2 * ε / 3) := by sorry

end ArbLindbladLearn
