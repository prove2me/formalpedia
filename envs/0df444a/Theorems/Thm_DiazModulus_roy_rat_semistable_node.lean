-- Prove2me | Theorems.Thm_DiazModulus_roy_rat_semistable_node
-- name    : DiazModulus.roy_rat_semistable_node
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:42.852771+00:00
-- url     : https://prove2.me/theorems/f397c65e-ab39-47fd-b3e5-e03d7fcf3b6c
-- title:
--   Roy's Th. 4 over ℚ, semistable case, from the multiplicity estimate: if d dim(U ∩ S) ≤ n dim S for all S rational over ℚ and n = dim U < d, then (d − n)ℓ ≤ dn for ℚ-free z in U ∩ (ℚ + ℒ)ᵈ
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). Write $\mathbb Q + \mathcal L$ for the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$; it consists of the numbers $q + \lambda$ with $q \in \mathbb Q$ and $\lambda \in \mathcal L$. A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   Assume the multiplicity estimate `hME`, and assume the conclusion of DiazModulus.roy_rat_slope_bound in every dimension $t < d$ (hypothesis `hIH`). Let $U \subseteq \mathbb C^d$ with $n = \dim U < d$ and $d \dim(U \cap S) \le n \dim S$ for every subspace $S \subseteq \mathbb C^d$ rational over $\mathbb Q$, and let $z_1, \dots, z_\ell \in U \cap (\mathbb Q + \mathcal L)^d$ be linearly independent over $\mathbb Q$. Then $(d - n)\,\ell \le d\,n$.
--
--   The multiplicity estimate is the explicit hypothesis `hME : MultiplicityEstimateElem` (proved on the platform as DiazModulus.multiplicityEstimateElem).
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4 (p. 34), semistable case, over F = ℚ (Remark (i), p. 37, with ℚ + ℒ in place of ℒ̃); M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 11.19 (p. 402) for (ℚ, ℚ + ℒ) in the same case. The route is that of DiazModulus.roy_semistable_node, over ℚ and with m = 1: DALAG Th. 11.21 (DiazModulus.linear_subgroup_transcendence) is applied once, and the periods are counted through one extra rational subspace. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rat_semistable_node (hME : MultiplicityEstimateElem) {d : ℕ}
    (hIH : ∀ t < d, ∀ (U' : Submodule ℂ (Fin t → ℂ)) (a b ℓ' : ℕ) (z' : Fin ℓ' → Fin t → ℂ),
        a < b → (∀ S : Submodule ℂ (Fin t → ℂ),
          Submodule.span ℂ {v : Fin t → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
          b * Module.finrank ℂ ↥(U' ⊓ S) ≤ a * Module.finrank ℂ ↥S) →
        (∀ i, z' i ∈ U') → (∀ i j, z' i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) →
        LinearIndependent ℚ z' → (b - a) * ℓ' ≤ b * Module.finrank ℂ ↥U')
    (U : Submodule ℂ (Fin d → ℂ)) (hUd : Module.finrank ℂ ↥U < d)
    (hss : ∀ S : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
      d * Module.finrank ℂ ↥(U ⊓ S) ≤ Module.finrank ℂ ↥U * Module.finrank ℂ ↥S)
    {ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U)
    (hz : ∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) (hzind : LinearIndependent ℚ z) :
    (d - Module.finrank ℂ ↥U) * ℓ ≤ d * Module.finrank ℂ ↥U := by
  sorry

end DiazModulus
