-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_3_5
-- name    : ArbLindbladLearn.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:30:39.405532+00:00
-- url     : https://prove2.me/theorems/0910a427-b700-4795-8752-b569f581258c
-- title:
--   Lemma 3.5 — heavy coherences imply heavy populations
-- statement:
--   Throughout, $\eta\in(0,\Lambda]$, $T=1/\Lambda$, $q=\min\{q'\in\mathbb N_{>0}:(q'+1)!\ge4\Lambda/\eta\}$, $t_j$ the Chebyshev–Lobatto nodes on $[0,T]$, $W=\sum_{j=1}^q|\ell_j'(0)|$, $p_j=|\ell_j'(0)|/W$, $\alpha=\eta^2/(4W^2)$ and $\mu(a)=\sum_{j=1}^qp_j\lambda_a(t_j)$ (eq. (18)); $\mathcal L$ is a Lindbladian with $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$.
--   1. For every nonidentity Pauli label $a$, if $|h_a|\ge\eta$ then $\mu(a)\ge\alpha$.
--   2. For every pair of nonidentity Pauli labels $a,b$, if $|\gamma_{ab}|\ge\eta$ then $\mu(a)\ge\alpha$ and $\mu(b)\ge\alpha$.
--
--   So every heavy coefficient is detected by sampling labels from $\mu$.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ (induced spectral norm, Hilbert–Schmidt adjoint) → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - encoding: λ_a(t) = g_aa(t) → the real part of g_aa(t); reason: g_aa(t) is real because J_t is Hermitian
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.5, p.21 (setup, eq. (18), p.21)

import Mathlib
import Definitions.Def_ArbLindbladLearn_muMix
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Lemma 3.5 (Heavy coherences imply heavy populations; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.21). For
every nonidentity Pauli label `a`, if `|h_a| ≥ η`, then `μ(a) ≥ α`. For every pair of nonidentity
Pauli labels `a, b`, if `|γ_ab| ≥ η`, then `μ(a) ≥ α` and `μ(b) ≥ α`.

**Formalization Note** The support-learning setup (p.21): `η ∈ (0, Λ]`, `T = 1/Λ`,
`q = min{q′ ∈ ℕ_{>0} : (q′+1)! ≥ 4Λ/η}` (`suppQ`), `W = Σ_{j=1}^q |ℓ′_j(0)|`, `p_j = |ℓ′_j(0)|/W`,
`α = η²/(4W²)` (`suppAlpha`) and `μ(a) = Σ_{j=1}^q p_j λ_a(t_j)` (eq. (18), `muMix`). The standing assumption `‖ℒ†‖_{∞→∞} ≤ Λ` (p.14) is `StrengthLE c Λ`; `IsLindbladCoeffs c` says
the Kossakowski matrix is Hermitian PSD (Definition 2.6). -/
theorem lemma_3_5 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) (Λ η : ℝ)
    (hΛ : StrengthLE c Λ) (hη : 0 < η) (hηΛ : η ≤ Λ) :
    (∀ a : Pauli n, a ≠ 0 → η ≤ |c.h a| → suppAlpha Λ η ≤ muMix c Λ η a) ∧
    (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 → η ≤ ‖c.γ a b‖ →
      suppAlpha Λ η ≤ muMix c Λ η a ∧ suppAlpha Λ η ≤ muMix c Λ η b) := by sorry

end ArbLindbladLearn
