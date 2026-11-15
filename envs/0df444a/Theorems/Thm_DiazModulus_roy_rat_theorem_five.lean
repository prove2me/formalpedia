-- Prove2me | Theorems.Thm_DiazModulus_roy_rat_theorem_five
-- name    : DiazModulus.roy_rat_theorem_five
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:45.849893+00:00
-- url     : https://prove2.me/theorems/4c28a586-d28d-4ff3-9d85-300a805566bc
-- title:
--   Roy 1992, Th. 5 over ℚ: if U ⊆ ℂᵈ meets ℚᵈ only in 0, any ℓ ℚ-free points of U ∩ (ℚ + ℒ)ᵈ have ℓ ≤ Σ nᵢdᵢ/(dᵢ − nᵢ) for a rational S ⊇ U and a decomposition (dim U, dim S) = Σ (nᵢ, dᵢ)
-- statement:
--   A *decomposition* of a pair $(n, d)$ of natural numbers is a finite list $(n_1, d_1), \dots, (n_k, d_k)$ of pairs of natural numbers with $0 < n_i < d_i$ for every $i$, $\sum_i n_i = n$ and $\sum_i d_i = d$ (the empty list, $k = 0$, decomposes $(0, 0)$ only).
--
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). Write $\mathbb Q + \mathcal L$ for the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$; it consists of the numbers $q + \lambda$ with $q \in \mathbb Q$ and $\lambda \in \mathcal L$. A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   Let $U \subseteq \mathbb C^d$ be a subspace that contains no non-zero rational vector, and let $z_1, \dots, z_\ell \in U \cap (\mathbb Q + \mathcal L)^d$ be linearly independent over $\mathbb Q$. Then there are a subspace $S \supseteq U$ of $\mathbb C^d$, rational over $\mathbb Q$, and a decomposition $(n_1, d_1), \dots, (n_k, d_k)$ of $(\dim U, \dim S)$ with
--   $$\ell \le \sum_{i=1}^k \frac{n_i d_i}{d_i - n_i}.$$
--   So $\ell \le \varphi(\dim U, \dim S)$, where Roy's $\varphi(n, d)$ is the largest value of this sum over the decompositions of $(n, d)$.
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 5 (p. 39) over F = ℚ, with ℚ + ℒ in place of ℒ̃: Roy's Remark (i) (p. 37) states his Th. 4 for any subfield F of Q̄, and Th. 5 follows from Th. 4 by his induction (pp. 39–40). Here in decomposition form, with a rational subspace S containing U in place of Roy's hypothesis that ℂᵈ is the least one; proved by an induction on d along a rational subspace of maximal slope, from DiazModulus.roy_rat_slope_bound, with the multiplicity estimate discharged by DiazModulus.multiplicityEstimateElem. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rat_theorem_five {d ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (hUQ : ∀ v ∈ U, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0)
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U)
    (hz : ∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) (hzind : LinearIndependent ℚ z) :
    ∃ (S : Submodule ℂ (Fin d → ℂ)) (D : List (ℕ × ℕ)),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S ∧ U ≤ S ∧
      (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥U ∧ (D.map Prod.snd).sum = Module.finrank ℂ ↥S ∧
      (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  sorry

end DiazModulus
