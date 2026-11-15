-- Prove2me | Theorems.Thm_DiazModulus_fv_rho_excess
-- name    : DiazModulus.fv_rho_excess
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:40.947863+00:00
-- url     : https://prove2.me/theorems/1dc8d0ca-a7e5-454e-9cda-ce75b22e2c79
-- title:
--   For Q̄-subspaces Y ⊆ Y′ of ℂⁿ, Y′ finite-dimensional, and ℂ-subspaces V ⊆ V′: ρ(Y′, V′) + ρ(Y, V) ≤ ρ(Y, V′) + ρ(Y′, V), where ρ(Z, W) = dim_Q̄ Z − dim_Q̄(Z ∩ W)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces. For a finite-dimensional $\overline{\mathbb Q}$-subspace $Z \subseteq \mathbb C^n$ and a $\mathbb C$-subspace $W \subseteq \mathbb C^n$ write $\rho(Z, W) = \dim_{\overline{\mathbb Q}} Z - \dim_{\overline{\mathbb Q}}(Z \cap W)$.
--
--   Let $Y \subseteq Y'$ be $\overline{\mathbb Q}$-subspaces of $\mathbb C^n$ with $Y'$ finite-dimensional (so $Y$ is finite-dimensional too), and let $V \subseteq V'$ be $\mathbb C$-subspaces of $\mathbb C^n$. Then
--   $$\rho(Y', V') + \rho(Y, V) \le \rho(Y, V') + \rho(Y', V).$$
--   At $V' = \mathbb C^n$, where both $\rho(\cdot, V')$ vanish, this is the monotonicity $\rho(Y, V) \le \rho(Y', V)$.
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5), for every Q̄-subspace Y: Grassmann's formula for Y and Y′ ∩ W, giving ρ(Y′, W) − ρ(Y, W) = dim Y′ − dim(Y + (Y′ ∩ W)). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_rho_excess {n : ℕ} (Y Y' : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥Y'] (hYY' : Y ≤ Y')
    (V V' : Submodule ℂ (Fin n → ℂ)) (hVV' : V ≤ V') :
    (Module.finrank (↥Qbar) ↥Y' - Module.finrank (↥Qbar) ↥(Y' ⊓ V'.restrictScalars (↥Qbar))) +
        (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar))) ≤
      (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V'.restrictScalars (↥Qbar))) +
        (Module.finrank (↥Qbar) ↥Y' - Module.finrank (↥Qbar) ↥(Y' ⊓ V.restrictScalars (↥Qbar))) := by
  sorry

end DiazModulus
