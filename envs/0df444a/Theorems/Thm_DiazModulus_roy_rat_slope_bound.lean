-- Prove2me | Theorems.Thm_DiazModulus_roy_rat_slope_bound
-- name    : DiazModulus.roy_rat_slope_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:41.065212+00:00
-- url     : https://prove2.me/theorems/8ffc063e-5b21-42e2-a852-c03082b8ce41
-- title:
--   Over ℚ: if b dim(U ∩ S) ≤ a dim S for every S ⊆ ℂᵈ rational over ℚ and a < b, then (b − a)ℓ ≤ b dim U for ℚ-free z₁, …, z_ℓ ∈ U ∩ (ℚ + ℒ)ᵈ
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). Write $\mathbb Q + \mathcal L$ for the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$; it consists of the numbers $q + \lambda$ with $q \in \mathbb Q$ and $\lambda \in \mathcal L$. A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   Assume the multiplicity estimate `hME`. Let $U \subseteq \mathbb C^d$ and natural numbers $a < b$ with $b \dim(U \cap S) \le a \dim S$ for every subspace $S \subseteq \mathbb C^d$ rational over $\mathbb Q$, and let $z_1, \dots, z_\ell \in U \cap (\mathbb Q + \mathcal L)^d$ be linearly independent over $\mathbb Q$. Then $(b - a)\,\ell \le b \dim U$. With $(a, b) = (\dim U, d)$ this is the semistable case of Roy's Theorem 4 over $\mathbb Q$: $\ell/(d + \ell) \le n/d$.
--
--   The multiplicity estimate is the explicit hypothesis `hME : MultiplicityEstimateElem` (proved on the platform as DiazModulus.multiplicityEstimateElem).
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4 (p. 34), semistable case, over F = ℚ (Remark (i), p. 37, with ℚ + ℒ in place of ℒ̃), in a form that passes to subspaces and quotients; the analogue over ℚ of DiazModulus.roy_slope_bound, by the same induction on d along a rational subspace of maximal slope. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rat_slope_bound (hME : MultiplicityEstimateElem) {d : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (a b ℓ : ℕ) (z : Fin ℓ → Fin d → ℂ) :
    a < b → (∀ S : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
        b * Module.finrank ℂ ↥(U ⊓ S) ≤ a * Module.finrank ℂ ↥S) →
      (∀ i, z i ∈ U) → (∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) →
      LinearIndependent ℚ z → (b - a) * ℓ ≤ b * Module.finrank ℂ ↥U := by
  sorry

end DiazModulus
