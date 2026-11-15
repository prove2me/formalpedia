-- Prove2me | Theorems.Thm_DiazModulus_variations_hyperplane_bound
-- name    : DiazModulus.variations_hyperplane_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:46.195339+00:00
-- url     : https://prove2.me/theorems/d14ed94d-aab4-48d4-8155-3221b7465225
-- title:
--   Waldschmidt 2005 (Variations), Th. 3.1: if a hyperplane V of ℂᵈ meets Q̄ᵈ only in 0, then V ∩ ℒ̃ᵈ has dimension at most d(d − 1) over Q̄
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $V \subseteq \mathbb C^d$ be a hyperplane ($\dim V + 1 = d$) that contains no non-zero vector with algebraic coordinates. Then $V \cap \widetilde{\mathcal L}^d$ is a finite-dimensional $\overline{\mathbb Q}$-vector space, and
--   $$\dim_{\overline{\mathbb Q}}\big(V \cap \widetilde{\mathcal L}^d\big) \le d\,(d - 1).$$
-- source:
--   M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Th. 3.1 (p. 347), the case of a hyperplane in Roy 1992, Th. 5 and DALAG Cor. 11.15. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem variations_hyperplane_bound {d : ℕ} (V : Submodule ℂ (Fin d → ℂ))
    (hV : Module.finrank ℂ ↥V + 1 = d) (hVQ : ∀ v ∈ V, (∀ i, v i ∈ Qbar) → v = 0) :
    FiniteDimensional (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ∧
      Module.finrank (↥Qbar)
          ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ≤
        d * (d - 1) := by
  sorry

end DiazModulus
