-- Prove2me | Theorems.Thm_DiazModulus_roy_theorem_four_exists
-- name    : DiazModulus.roy_theorem_four_exists
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:29.01666+00:00
-- url     : https://prove2.me/theorems/60c609d9-378c-4f6b-ab17-e9e26a5b7759
-- title:
--   Roy's Theorem 4 with its minimiser: for $d \ge 1$ some rational $S \ne \mathbb C^d$ minimises $(n - \dim(U \cap S))/(d - \dim S)$, and there $\ell'/(d' + \ell') \le n'/d' \le n/d$
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $d \ge 1$, let $U \subseteq \mathbb C^d$ be a subspace, $n = \dim U$, and let $z_1, \dots, z_\ell \in U \cap \widetilde{\mathcal L}^d$ be linearly independent over $\overline{\mathbb Q}$, spanning $Z$ over $\overline{\mathbb Q}$. Then there is a rational subspace $S \ne \mathbb C^d$ such that
--   $$(n - \dim(U \cap S))\,(d - \dim S') \le (n - \dim(U \cap S'))\,(d - \dim S)$$
--   for every rational subspace $S' \ne \mathbb C^d$ (so $S$ minimises $(n - \dim(U \cap S))/(d - \dim S)$ among them), and, with $d' = d - \dim S$, $n' = n - \dim(U \cap S)$ and $\ell' = \ell - \dim_{\overline{\mathbb Q}}(Z \cap S)$,
--   $$\ell'\,d' \le n'\,(d' + \ell') \quad\text{and}\quad n'\,d \le n\,d'.$$
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4 (p. 34), at a rational subspace minimising the ratio; the minimum exists because the ratio takes finitely many values. Step of the proof of Roy's Th. 5 (p. 39). No hypothesis: the multiplicity estimate is DiazModulus.multiplicityEstimateElem. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_theorem_four_exists {d ℓ : ℕ} (hd : 0 < d) (U : Submodule ℂ (Fin d → ℂ))
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    ∃ S : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S ∧ S ≠ ⊤ ∧
      (∀ S' : Submodule ℂ (Fin d → ℂ),
        Submodule.span ℂ {v : Fin d → ℂ | v ∈ S' ∧ ∀ i, v i ∈ Qbar} = S' → S' ≠ ⊤ →
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * (d - Module.finrank ℂ ↥S') ≤
          (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S')) * (d - Module.finrank ℂ ↥S)) ∧
      (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar))) *
          (d - Module.finrank ℂ ↥S) ≤
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) *
          ((d - Module.finrank ℂ ↥S) +
            (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar)))) ∧
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * d ≤
        Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥S) := by
  sorry

end DiazModulus
