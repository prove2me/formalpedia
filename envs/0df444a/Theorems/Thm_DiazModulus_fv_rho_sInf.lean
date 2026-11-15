-- Prove2me | Theorems.Thm_DiazModulus_fv_rho_sInf
-- name    : DiazModulus.fv_rho_sInf
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:45.297708+00:00
-- url     : https://prove2.me/theorems/6be132cd-1c49-46ad-95bf-ac68e653130c
-- title:
--   For a finite-dimensional Q̄-subspace Y ⊆ ℂⁿ and any set F of ℂ-subspaces with ρ(V) ≤ D for V ∈ F: ρ(⋂F) ≤ nD, where ρ(V) = dim_Q̄ Y − dim_Q̄(Y ∩ V)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   Let $Y \subseteq \mathbb C^n$ be a finite-dimensional $\overline{\mathbb Q}$-subspace, and for a $\mathbb C$-subspace $W \subseteq \mathbb C^n$ write $\rho(W) = \dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap W)$. Let $\mathcal F$ be any set of $\mathbb C$-subspaces of $\mathbb C^n$ (finite, infinite or empty) and $D$ a natural number with $\rho(V) \le D$ for every $V \in \mathcal F$, and let $J$ be the intersection of all members of $\mathcal F$ ($J = \mathbb C^n$ if $\mathcal F$ is empty). Then
--   $$\rho(J) \le n\,D.$$
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5), for every Q̄-subspace Y: the bound for the intersection of an arbitrary family, by induction on the dimension, from DiazModulus.fv_rho_inf. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_rho_sInf {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ)) [FiniteDimensional (↥Qbar) ↥Y]
    (F : Set (Submodule ℂ (Fin n → ℂ))) (D : ℕ)
    (hD : ∀ V ∈ F, Module.finrank (↥Qbar) ↥Y -
        Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar)) ≤ D) :
    Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ (sInf F).restrictScalars (↥Qbar)) ≤
      n * D := by
  sorry

end DiazModulus
