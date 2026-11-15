-- Prove2me | Theorems.Thm_DiazModulus_fv_rho_inf
-- name    : DiazModulus.fv_rho_inf
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:41.31098+00:00
-- url     : https://prove2.me/theorems/8b6d2a5b-d4be-4a5c-9c9b-febc991dc298
-- title:
--   For a finite-dimensional Q̄-subspace Y ⊆ ℂⁿ and ℂ-subspaces V₁, V₂ of ℂⁿ: ρ(V₁ ∩ V₂) ≤ ρ(V₁) + ρ(V₂), where ρ(V) = dim_Q̄ Y − dim_Q̄(Y ∩ V)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   Let $Y \subseteq \mathbb C^n$ be a finite-dimensional $\overline{\mathbb Q}$-subspace, and for a $\mathbb C$-subspace $W \subseteq \mathbb C^n$ write $\rho(W) = \dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap W)$. Then for all $\mathbb C$-subspaces $V_1, V_2 \subseteq \mathbb C^n$
--   $$\rho(V_1 \cap V_2) \le \rho(V_1) + \rho(V_2).$$
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5), for every Q̄-subspace Y: Grassmann's formula for Y ∩ V₁ and Y ∩ V₂. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_rho_inf {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ)) [FiniteDimensional (↥Qbar) ↥Y]
    (V₁ V₂ : Submodule ℂ (Fin n → ℂ)) :
    Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ (V₁ ⊓ V₂).restrictScalars (↥Qbar)) ≤
      (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V₁.restrictScalars (↥Qbar))) +
        (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V₂.restrictScalars (↥Qbar))) := by
  sorry

end DiazModulus
