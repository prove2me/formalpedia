-- Prove2me | Theorems.Thm_DiazModulus_roy_theorem_four
-- name    : DiazModulus.roy_theorem_four
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:47:31.968668+00:00
-- url     : https://prove2.me/theorems/7ba07b5d-f9b6-420a-8d92-fa5e712f7de8
-- title:
--   Roy 1992, Theorem 4, for $(\overline{\mathbb Q}, \widetilde{\mathcal L})$: at a rational $S$ minimising $(n - \dim(U \cap S))/(d - \dim S)$, $\ell'/(d' + \ell') \le n'/d' \le n/d$
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Assume the multiplicity estimate `hME`. Let $U \subseteq \mathbb C^d$, $n = \dim U$, and $z_1, \dots, z_\ell \in U \cap \widetilde{\mathcal L}^d$ linearly independent over $\overline{\mathbb Q}$, spanning $Z$. Let $S \ne \mathbb C^d$ be rational and minimise $(n - \dim(U \cap S))/(d - \dim S)$ among rational subspaces $\ne \mathbb C^d$. With $d' = d - \dim S$, $n' = n - \dim(U \cap S)$ and $\ell' = \ell - \dim_{\overline{\mathbb Q}}(Z \cap S)$ (the dimensions of the images under the quotient map by $S$):
--   $$\ell'\,d' \le n'\,(d' + \ell') \quad\text{and}\quad n'\,d \le n\,d'.$$
--
--   The multiplicity estimate is the explicit hypothesis `hME : MultiplicityEstimateElem` (proved on the platform as DiazModulus.multiplicityEstimateElem).
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4 (§4, p. 34), for K = Q̄, ℒ̃ = Q̄ + Q̄ℒ; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 11.19 (§11.6.2, p. 402). Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_theorem_four (hME : MultiplicityEstimateElem) {d ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z)
    (S : Submodule ℂ (Fin d → ℂ)) (hSrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S) (hStop : S ≠ ⊤)
    (hmin : ∀ S' : Submodule ℂ (Fin d → ℂ), Submodule.span ℂ {v : Fin d → ℂ | v ∈ S' ∧ ∀ i, v i ∈ Qbar} = S' → S' ≠ ⊤ →
      (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S)) * (d - Module.finrank ℂ ↥(S')) ≤
        (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S')) * (d - Module.finrank ℂ ↥(S))) :
    (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar))) * (d - Module.finrank ℂ ↥(S)) ≤
        (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S)) * ((d - Module.finrank ℂ ↥(S)) + (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar)))) ∧
      (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S)) * d ≤ Module.finrank ℂ ↥(U) * (d - Module.finrank ℂ ↥(S)) := by
  sorry

end DiazModulus
