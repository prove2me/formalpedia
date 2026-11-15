-- Prove2me | Theorems.Thm_DiazModulus_roy_rat_theorem_four
-- name    : DiazModulus.roy_rat_theorem_four
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-15T05:43:10.715122+00:00
-- url     : https://prove2.me/theorems/21bfecda-b526-498c-aed6-d3cc4ab760fe
-- title:
--   Roy 1992, Th. 4 over ℚ, minimal-ratio form: for ℚ-free z in U ∩ (ℚ + ℒ)ᵈ and S ≠ ℂᵈ rational over ℚ of minimal ratio n′/d′, then ℓ′/(d′ + ℓ′) ≤ n′/d′ ≤ n/d
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). Write $\mathbb Q + \mathcal L$ for the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$; it consists of the numbers $q + \lambda$ with $q \in \mathbb Q$ and $\lambda \in \mathcal L$. A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   For subspaces $U, S \subseteq \mathbb C^d$ with $S \ne \mathbb C^d$ write $n'(S) = \dim U - \dim(U \cap S)$ and $d'(S) = d - \dim S$. A subspace $S \ne \mathbb C^d$ rational over $\mathbb Q$ has *minimal ratio* if $n'(S)\,d'(S') \le n'(S')\,d'(S)$ for every subspace $S' \ne \mathbb C^d$ rational over $\mathbb Q$, that is, if it minimises $n'/d'$ among them.
--
--   Let $U \subseteq \mathbb C^d$ be a subspace with $n = \dim U$, let $z_1, \dots, z_\ell \in U \cap (\mathbb Q + \mathcal L)^d$ be linearly independent over $\mathbb Q$, and let $S \ne \mathbb C^d$ be rational over $\mathbb Q$ of minimal ratio. Put $n' = n'(S)$, $d' = d'(S)$ and $\ell' = \ell - \dim_{\mathbb Q}\big(\mathrm{span}_{\mathbb Q}(z) \cap S\big)$. Then
--   $$\ell'\,d' \le n'\,(d' + \ell') \qquad\text{and}\qquad n'\,d \le n\,d',$$
--   that is, $\ell'/(d' + \ell') \le n'/d' \le n/d$. The statement has no hypothesis: the multiplicity estimate it rests on is proved.
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4 (p. 34) over F = ℚ (Remark (i), p. 37, with ℚ + ℒ in place of ℒ̃), in its minimal-ratio form; the analogue over ℚ of DiazModulus.roy_theorem_four, proved from DiazModulus.roy_rat_slope_bound and DiazModulus.roy_rat_adapted_basis, with the multiplicity estimate discharged by DiazModulus.multiplicityEstimateElem. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rat_theorem_four {d ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U)
    (hz : ∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) (hzind : LinearIndependent ℚ z)
    (S : Submodule ℂ (Fin d → ℂ))
    (hSrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S) (hStop : S ≠ ⊤)
    (hmin : ∀ S' : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S' ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S' → S' ≠ ⊤ →
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * (d - Module.finrank ℂ ↥S') ≤
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S')) * (d - Module.finrank ℂ ↥S)) :
    (ℓ - Module.finrank ℚ ↥(Submodule.span ℚ (Set.range z) ⊓ S.restrictScalars ℚ)) *
        (d - Module.finrank ℂ ↥S) ≤
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) *
        ((d - Module.finrank ℂ ↥S) +
          (ℓ - Module.finrank ℚ ↥(Submodule.span ℚ (Set.range z) ⊓ S.restrictScalars ℚ))) ∧
    (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * d ≤
      Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥S) := by
  sorry

end DiazModulus
