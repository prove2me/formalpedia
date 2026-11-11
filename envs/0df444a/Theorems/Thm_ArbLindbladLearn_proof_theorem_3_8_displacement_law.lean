-- Prove2me | Theorems.Thm_ArbLindbladLearn_proof_theorem_3_8_displacement_law
-- name    : ArbLindbladLearn.proof_theorem_3_8_displacement_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:30:11.668223+00:00
-- url     : https://prove2.me/theorems/68ee1a88-38de-45d9-b92d-8d17c6149845
-- title:
--   Proof of Theorem 3.8 (p.24) — a round records $u\oplus v$ with law $\mu_X$ (resp. $\mu_Z$)
-- statement:
--   Throughout, $\eta\in(0,\Lambda]$, $T=1/\Lambda$, $q=\min\{q'\in\mathbb N_{>0}:(q'+1)!\ge4\Lambda/\eta\}$, $t_j$ the Chebyshev–Lobatto nodes on $[0,T]$, $W=\sum_{j=1}^q|\ell_j'(0)|$, $p_j=|\ell_j'(0)|/W$, $\alpha=\eta^2/(4W^2)$ and $\mu(a)=\sum_{j=1}^qp_j\lambda_a(t_j)$ (eq. (18)); $\mathcal L$ is a Lindbladian with $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$.
--   A computational-basis round of Algorithm 1 samples $j$ with probability $p_j$ and a uniform label $c$, prepares $|u\rangle$, applies $P_c$, evolves under $e^{t_j\mathcal L}$, applies $P_c$, and measures in the computational basis with outcome $v$. Then $u\oplus v=x$ has probability
--   $$\mu_X(x)=\sum_{z\in\mathbb F_2^n}\mu(z,x).$$
--   An $X$-basis round (preparing $|u\rangle_X=H^{\otimes n}|u\rangle$ and measuring in the $X$ basis) records $u\oplus v=z$ with probability $\mu_Z(z)=\sum_{x\in\mathbb F_2^n}\mu(z,x)$.
--
--   This is the step of the proof of Theorem 3.8 that connects the experiments to the marginals of $\mu$ (through Lemmas 3.6 and 3.7).
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ (induced spectral norm, Hilbert–Schmidt adjoint) → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - generalization: the law of u ⊕ v for a round whose u is uniform on {0,1}ⁿ → the law for every fixed u; reason: the per-u law is the same for every u, so averaging over the uniform u gives the page's statement
--   - encoding: the probability of outcome v → Re⟨v|σ|v⟩ (resp. Re ⟨v|_X σ |v⟩_X) for the post-experiment state σ, summed with weights p_j·4⁻ⁿ; reason: Born rule; the expression is real
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), proof of Theorem 3.8, p.24; Lemma 3.7, p.23; Algorithm 1 lines 5–8, 11–14, p.23

import Mathlib
import Definitions.Def_ArbLindbladLearn_muMix
import Definitions.Def_ArbLindbladLearn_xPart
import Definitions.Def_ArbLindbladLearn_xBasisVec
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Proof of Theorem 3.8, displacement law (Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.24; with Lemma 3.7,
p.23, and Algorithm 1, lines 5–8 and 11–14, p.23). A computational-basis round records
`u ⊕ v = x` with probability `μ_X(x) = Σ_z μ(z, x)`, and an `X`-basis round records `u ⊕ v = z` with
probability `μ_Z(z) = Σ_x μ(z, x)`.

A round samples `j ∈ [q]` with probability `p_j`, a uniform label `w ∈ 𝔽₂²ⁿ` and a bit string `u`;
prepares `|u⟩` (resp. `|u⟩_X = H^{⊗n}|u⟩`), applies `P_w`, evolves under `e^{t_jℒ}`, applies `P_w`, and
measures in the computational (resp. `X`) basis with outcome `v`. The event `u ⊕ v = x` is the
outcome `v = u ⊕ x`.

**Formalization Note** The support-learning setup (p.21): `η ∈ (0, Λ]`, `T = 1/Λ`,
`q = min{q′ ∈ ℕ_{>0} : (q′+1)! ≥ 4Λ/η}` (`suppQ`), `W = Σ_{j=1}^q |ℓ′_j(0)|`, `p_j = |ℓ′_j(0)|/W`,
`α = η²/(4W²)` (`suppAlpha`) and `μ(a) = Σ_{j=1}^q p_j λ_a(t_j)` (eq. (18), `muMix`). The standing assumption `‖ℒ†‖_{∞→∞} ≤ Λ` (p.14) is `StrengthLE c Λ`; `IsLindbladCoeffs c` says
the Kossakowski matrix is Hermitian PSD (Definition 2.6). The laws are stated for every fixed `u`, before averaging over
the uniform `u` of Algorithm 1; `μ_X(x)` sums `μ` over the labels with `x`-part `x` (`xPart`) and
`μ_Z(z)` over the labels with `z`-part `z` (`zPart`). The Born probability of outcome `v` for the
state `σ` is `Re⟨v|σ|v⟩` (resp. `Re ⟨v|_X σ |v⟩_X`). -/
theorem proof_theorem_3_8_displacement_law {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c)
    (Λ η : ℝ) (hΛ : StrengthLE c Λ) (hη : 0 < η) (hηΛ : η ≤ Λ) (u x z : Qubits n) :
    (∑ j ∈ Finset.Icc 1 (suppQ Λ η), suppP Λ η j * (((4 : ℝ) ^ n)⁻¹ * ∑ w : Pauli n,
        (quadForm (basisVec (xorBits u x))
          (pauliMatrix w *
            applySuper (evolution (gen c) (chebNode (suppQ Λ η) (suppT Λ) j))
              (pauliMatrix w * outer (basisVec u) (basisVec u) * pauliMatrix w) *
            pauliMatrix w)).re) =
      ∑ a ∈ Finset.univ.filter (fun a : Pauli n => xPart a = x), muMix c Λ η a) ∧
    (∑ j ∈ Finset.Icc 1 (suppQ Λ η), suppP Λ η j * (((4 : ℝ) ^ n)⁻¹ * ∑ w : Pauli n,
        (quadForm (xBasisVec (xorBits u z))
          (pauliMatrix w *
            applySuper (evolution (gen c) (chebNode (suppQ Λ η) (suppT Λ) j))
              (pauliMatrix w * outer (xBasisVec u) (xBasisVec u) * pauliMatrix w) *
            pauliMatrix w)).re) =
      ∑ a ∈ Finset.univ.filter (fun a : Pauli n => zPart a = z), muMix c Λ η a) := by sorry

end ArbLindbladLearn
