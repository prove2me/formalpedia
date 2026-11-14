-- Prove2me | Theorems.Thm_DiazModulus_roy_slope_bound
-- name    : DiazModulus.roy_slope_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:47:22.721853+00:00
-- url     : https://prove2.me/theorems/824e3a3c-be85-43a2-a227-babdf14f7da6
-- title:
--   If $b \dim(U \cap S) \le a \dim S$ for every rational $S$ and $a < b$, then $(b - a)\,\ell \le b \dim U$ for $\overline{\mathbb Q}$-free $z_1, \dots, z_\ell \in U \cap \widetilde{\mathcal L}^d$
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Assume the multiplicity estimate `hME`. Let $U \subseteq \mathbb C^d$ and natural numbers $a < b$ with $b \dim(U \cap S) \le a \dim S$ for every rational $S \subseteq \mathbb C^d$, and $z_1, \dots, z_\ell \in U \cap \widetilde{\mathcal L}^d$ are linearly independent over $\overline{\mathbb Q}$. Then $(b - a)\,\ell \le b \dim U$. With $(a, b) = (\dim U, d)$ this is the first case of Roy's Theorem 4: $\ell/(d + \ell) \le n/d$.
--
--   The multiplicity estimate is the explicit hypothesis `hME : MultiplicityEstimateElem` (proved on the platform as DiazModulus.multiplicityEstimateElem).
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4, first case (p. 34), in a form that passes to subspaces and quotients; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 11.19. The route is the Diaz modulus mission's: an induction on d that splits along a rational subspace of maximal slope and applies DALAG Th. 11.21 once at each semistable step, counting the periods through one extra rational subspace; DALAG and Roy argue instead through Th. 11.5 (3′) and Lemma 11.24, respectively Roy's Th. 2. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_slope_bound (hME : MultiplicityEstimateElem) {d : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (a b ℓ : ℕ) (z : Fin ℓ → Fin d → ℂ) :
    a < b → (∀ S : Submodule ℂ (Fin d → ℂ), Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S →
          b * Module.finrank ℂ ↥(U ⊓ S) ≤ a * Module.finrank ℂ ↥(S)) →
        (∀ i, z i ∈ U) → (∀ i j, z i j ∈ LogAlgTilde) → LinearIndependent (↥Qbar) z →
        (b - a) * ℓ ≤ b * Module.finrank ℂ ↥(U) := by
  sorry

end DiazModulus
