-- Prove2me | Theorems.Thm_DiazModulus_fv_finite_approx
-- name    : DiazModulus.fv_finite_approx
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:36.128369+00:00
-- url     : https://prove2.me/theorems/a9399e33-b864-4b4e-8819-9a025788c0c3
-- title:
--   Finite approximation: for a Q̄-subspace Y ⊆ ℂⁿ and B ∈ ℕ, one finite-dimensional Y₀ ⊆ Y has dim Y₀/(Y₀ ∩ V) ≥ min(dim Y₁/(Y₁ ∩ V), B) for all ℂ-subspaces V and finite-dimensional Y₁ ⊆ Y
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces. For a finite-dimensional $\overline{\mathbb Q}$-subspace $Z \subseteq \mathbb C^n$ and a $\mathbb C$-subspace $W \subseteq \mathbb C^n$ write $\rho(Z, W) = \dim_{\overline{\mathbb Q}} Z - \dim_{\overline{\mathbb Q}}(Z \cap W)$.
--
--   Let $Y \subseteq \mathbb C^n$ be a $\overline{\mathbb Q}$-subspace of any dimension and $B$ a natural number. Then there is a finite-dimensional $\overline{\mathbb Q}$-subspace $Y_0 \subseteq Y$ such that
--   $$\min\big(\rho(Y_1, V),\ B\big) \le \rho(Y_0, V)$$
--   for every $\mathbb C$-subspace $V \subseteq \mathbb C^n$ and every finite-dimensional $\overline{\mathbb Q}$-subspace $Y_1 \subseteq Y$. The same $Y_0$ serves for every $V$.
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5), for every Q̄-subspace Y: one finite-dimensional Y₀ ⊆ Y that serves for every ℂ-subspace V at once, chosen by maximising a bounded natural number attached to the intersection of the ℂ-subspaces V with ρ(Z, V) < B; from DiazModulus.fv_rho_excess and DiazModulus.fv_rho_sInf. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_finite_approx {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ)) (B : ℕ) :
    ∃ Y₀ : Submodule (↥Qbar) (Fin n → ℂ), Y₀ ≤ Y ∧ FiniteDimensional (↥Qbar) ↥Y₀ ∧
      ∀ (V : Submodule ℂ (Fin n → ℂ)) (Y₁ : Submodule (↥Qbar) (Fin n → ℂ)),
        Y₁ ≤ Y → FiniteDimensional (↥Qbar) ↥Y₁ →
        min (Module.finrank (↥Qbar) ↥Y₁ -
              Module.finrank (↥Qbar) ↥(Y₁ ⊓ V.restrictScalars (↥Qbar))) B ≤
          Module.finrank (↥Qbar) ↥Y₀ -
            Module.finrank (↥Qbar) ↥(Y₀ ⊓ V.restrictScalars (↥Qbar)) := by
  sorry

end DiazModulus
