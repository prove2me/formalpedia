-- Prove2me | Theorems.Thm_DiazModulus_roy_theorem_five
-- name    : DiazModulus.roy_theorem_five
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:25.214102+00:00
-- url     : https://prove2.me/theorems/79c50e32-fba2-4621-b5fb-b8e6e3aca4b4
-- title:
--   Roy 1992, Th. 5: if U ⊆ ℂᵈ meets Q̄ᵈ only in 0 and has rational hull ℂᵈ, any ℓ Q̄-free points of U ∩ ℒ̃ᵈ satisfy ℓ ≤ Σ nᵢdᵢ/(dᵢ − nᵢ) for a decomposition (dim U, d) = Σ (nᵢ, dᵢ)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   A *decomposition* of a pair $(n, d)$ of natural numbers is a finite list $(n_1, d_1), \dots, (n_k, d_k)$ of pairs of natural numbers with $0 < n_i < d_i$ for every $i$, $\sum_i n_i = n$ and $\sum_i d_i = d$ (the empty list, $k = 0$, decomposes $(0, 0)$ only).
--
--   Let $U \subseteq \mathbb C^d$ be a subspace that contains no non-zero vector with algebraic coordinates, such that $\mathbb C^d$ is the only rational subspace of $\mathbb C^d$ containing $U$, and let $z_1, \dots, z_\ell \in U \cap \widetilde{\mathcal L}^d$ be linearly independent over $\overline{\mathbb Q}$. Then $0 < \dim U < d$ if $d \ge 1$, and there is a decomposition $(n_1, d_1), \dots, (n_k, d_k)$ of $(\dim U, d)$ with
--   $$\ell \le \sum_{i=1}^k \frac{n_i d_i}{d_i - n_i}.$$
--   Roy's $\varphi(n, d)$ is the largest value of this sum over the decompositions of $(n, d)$, so $\ell \le \varphi(\dim U, d)$ for every such family. The bound for $\dim_{\overline{\mathbb Q}}(U \cap \widetilde{\mathcal L}^d)$ itself, with its finiteness, is the case $\mathbb C^d$ of DiazModulus.roy_theorem_five_dmin.
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 5 (p. 39), with one decomposition in place of Roy's φ(n, d), the largest value over all decompositions (pp. 38–39); the proof is Roy's induction on d (pp. 39–40). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_theorem_five {d ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (hUQ : ∀ v ∈ U, (∀ i, v i ∈ Qbar) → v = 0)
    (hhull : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U ≤ T → T = ⊤)
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    (0 < d → 0 < Module.finrank ℂ ↥U ∧ Module.finrank ℂ ↥U < d) ∧
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥U ∧ (D.map Prod.snd).sum = d ∧
      (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  sorry

end DiazModulus
