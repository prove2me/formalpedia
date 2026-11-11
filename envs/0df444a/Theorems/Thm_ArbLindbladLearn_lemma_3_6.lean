-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_3_6
-- name    : ArbLindbladLearn.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:53.282535+00:00
-- url     : https://prove2.me/theorems/93369b74-0de0-4d4f-b368-17de005a71aa
-- title:
--   Lemma 3.6 — the twirled channel is the Pauli channel of $\mu$
-- statement:
--   Throughout, $\eta\in(0,\Lambda]$, $T=1/\Lambda$, $q=\min\{q'\in\mathbb N_{>0}:(q'+1)!\ge4\Lambda/\eta\}$, $t_j$ the Chebyshev–Lobatto nodes on $[0,T]$, $W=\sum_{j=1}^q|\ell_j'(0)|$, $p_j=|\ell_j'(0)|/W$, $\alpha=\eta^2/(4W^2)$ and $\mu(a)=\sum_{j=1}^qp_j\lambda_a(t_j)$ (eq. (18)); $\mathcal L$ is a Lindbladian with $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$.
--   The twirled and mixed channel
--   $$\overline{\mathcal E}(\rho)=\sum_{j=1}^q\frac{p_j}{4^n}\sum_{c\in\mathbb F_2^{2n}}P_c\,e^{t_j\mathcal L}(P_c\rho P_c)\,P_c$$
--   satisfies
--   $$\overline{\mathcal E}(\rho)=\sum_{a\in\mathbb F_2^{2n}}\mu(a)\,P_a\rho P_a .$$
--
--   This lets the support-learning experiments sample the distribution $\mu$.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ (induced spectral norm, Hilbert–Schmidt adjoint) → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - encoding: λ_a(t_j) = g_aa(t_j) in μ → the real part of g_aa(t_j); reason: g_aa is real; same values
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.6, p.22

import Mathlib
import Definitions.Def_ArbLindbladLearn_twirled
import Definitions.Def_ArbLindbladLearn_muMix
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Lemma 3.6 (Twirled channel realizing the mixture; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.22). The
channel `ℰ(ρ) = Σ_{j=1}^q (p_j/4ⁿ) Σ_{c ∈ 𝔽₂²ⁿ} P_c e^{t_jℒ}(P_c ρ P_c) P_c` obtained by twirling and
mixing the semigroup satisfies `ℰ(ρ) = Σ_{a ∈ 𝔽₂²ⁿ} μ(a) P_a ρ P_a`.

**Formalization Note** The support-learning setup (p.21): `η ∈ (0, Λ]`, `T = 1/Λ`,
`q = min{q′ ∈ ℕ_{>0} : (q′+1)! ≥ 4Λ/η}` (`suppQ`), `W = Σ_{j=1}^q |ℓ′_j(0)|`, `p_j = |ℓ′_j(0)|/W`,
`α = η²/(4W²)` (`suppAlpha`) and `μ(a) = Σ_{j=1}^q p_j λ_a(t_j)` (eq. (18), `muMix`). The standing assumption `‖ℒ†‖_{∞→∞} ≤ Λ` (p.14) is `StrengthLE c Λ`; `IsLindbladCoeffs c` says
the Kossakowski matrix is Hermitian PSD (Definition 2.6). The identity is stated for every operator `ρ`. -/
theorem lemma_3_6 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) (Λ η : ℝ)
    (hΛ : StrengthLE c Λ) (hη : 0 < η) (hηΛ : η ≤ Λ) (ρ : Op (Qubits n)) :
    twirled c Λ η ρ =
      ∑ a : Pauli n, (muMix c Λ η a : ℂ) • (pauliMatrix a * ρ * pauliMatrix a) := by sorry

end ArbLindbladLearn
