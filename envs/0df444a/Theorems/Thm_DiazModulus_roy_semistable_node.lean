-- Prove2me | Theorems.Thm_DiazModulus_roy_semistable_node
-- name    : DiazModulus.roy_semistable_node
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:47:09.974502+00:00
-- url     : https://prove2.me/theorems/429169c3-3d91-4c3c-a437-df6704729413
-- title:
--   Roy's Theorem 4, semistable case, from the multiplicity estimate: if $d \dim(U \cap S) \le n \dim S$ for all rational $S$ and $n = \dim U < d$, then $(d - n)\,\ell \le dn$
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Assume the multiplicity estimate `hME`, and assume the conclusion of `DiazModulus.roy_slope_bound` in every dimension $t < d$ (hypothesis `hIH`). Let $U \subseteq \mathbb C^d$ with $n = \dim U < d$ and $d \dim(U \cap S) \le n \dim S$ for every rational $S \subseteq \mathbb C^d$, and $z_1, \dots, z_\ell \in U \cap \widetilde{\mathcal L}^d$ are linearly independent over $\overline{\mathbb Q}$. Then $(d - n)\,\ell \le d\,n$.
--
--   The multiplicity estimate is the explicit hypothesis `hME : MultiplicityEstimateElem` (proved on the platform as DiazModulus.multiplicityEstimateElem).
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4, first case; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 11.19 (§11.6.2), first case, through M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (§11.7.1), as DiazModulus.linear_subgroup_transcendence, applied once. The route is the Diaz modulus mission's: an induction on d that splits along a rational subspace of maximal slope and applies DALAG Th. 11.21 once at each semistable step, counting the periods through one extra rational subspace; DALAG and Roy argue instead through Th. 11.5 (3′) and Lemma 11.24, respectively Roy's Th. 2. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_semistable_node (hME : MultiplicityEstimateElem) {d : ℕ}
    (hIH : ∀ t < d, ∀ (U' : Submodule ℂ (Fin t → ℂ)) (a b ℓ' : ℕ) (z' : Fin ℓ' → Fin t → ℂ),
        a < b → (∀ S : Submodule ℂ (Fin t → ℂ), Submodule.span ℂ {v : Fin t → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S →
          b * Module.finrank ℂ ↥(U' ⊓ S) ≤ a * Module.finrank ℂ ↥(S)) →
        (∀ i, z' i ∈ U') → (∀ i j, z' i j ∈ LogAlgTilde) → LinearIndependent (↥Qbar) z' →
        (b - a) * ℓ' ≤ b * Module.finrank ℂ ↥(U'))
    (U : Submodule ℂ (Fin d → ℂ)) (hUd : Module.finrank ℂ ↥(U) < d)
    (hss : ∀ S : Submodule ℂ (Fin d → ℂ), Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S →
      d * Module.finrank ℂ ↥(U ⊓ S) ≤ Module.finrank ℂ ↥(U) * Module.finrank ℂ ↥(S))
    {ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    (d - Module.finrank ℂ ↥(U)) * ℓ ≤ d * Module.finrank ℂ ↥(U) := by
  sorry

end DiazModulus
