-- Prove2me | Theorems.Thm_DiazModulus_fv_semistable_core
-- name    : DiazModulus.fv_semistable_core
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:38.294228+00:00
-- url     : https://prove2.me/theorems/56eb2d08-5555-4e00-9652-7d3ad7447ad1
-- title:
--   The semistable case, relative form: if X₀ ⊆ W₀ is semistable relative to W₀, n₀ = dim_ℂ W₀ < d₀ = dim_Q̄ X₀ and X₀ · Y ⊆ ℒ̃, then μ(Y, ℂⁿ) ≤ d₀/(d₀ − n₀)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $u, v \in \mathbb C^n$, $u \cdot v = \sum_k u_k v_k$ is the bilinear dot product (not the Hermitian one). For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   For a finite-dimensional $\overline{\mathbb Q}$-subspace $Y \subseteq \mathbb C^n$ with $n \ge 1$, $\mu(Y, \mathbb C^n)$ is the minimum of $\big(\dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap V)\big)/(n - \dim_{\mathbb C} V)$ over the $\mathbb C$-subspaces $V \ne \mathbb C^n$ (Further variations, p. 4); the ratio takes finitely many values, so the minimum is attained.
--
--   Let $W_0 \subseteq \mathbb C^n$ be a $\mathbb C$-subspace, $n_0 = \dim_{\mathbb C} W_0$, and let $X_0, Y \subseteq \mathbb C^n$ be finite-dimensional $\overline{\mathbb Q}$-subspaces with $X_0 \subseteq W_0$ and $d_0 = \dim_{\overline{\mathbb Q}} X_0 > n_0$. Assume that $n_0 \dim_{\overline{\mathbb Q}}(X_0 \cap W) \le d_0 \dim_{\mathbb C} W$ for every $\mathbb C$-subspace $W \subseteq \mathbb C^n$ ($X_0$ is semistable relative to $W_0$), and that $x \cdot y \in \widetilde{\mathcal L}$ for all $x \in X_0$ and $y \in Y$. Then there is a $\mathbb C$-subspace $V \ne \mathbb C^n$ with
--   $$(d_0 - n_0)\big(\dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap V)\big) \le d_0\,(n - \dim_{\mathbb C} V),$$
--   that is, $\mu(Y, \mathbb C^n) \le d_0/(d_0 - n_0)$.
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1: the semistable case (p. 6; M. Waldschmidt, Transcendance et exponentielles en plusieurs variables, Invent. Math. 63 (1981), 97–127, Prop. 6.1), here for a subspace X₀ of W₀ semistable relative to W₀, with Roy's Corollary 1 used once. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_semistable_core {n : ℕ} (W₀ : Submodule ℂ (Fin n → ℂ))
    (X₀ Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X₀] [FiniteDimensional (↥Qbar) ↥Y]
    (hX₀ : ∀ x ∈ X₀, x ∈ W₀)
    (hss : ∀ W : Submodule ℂ (Fin n → ℂ),
      Module.finrank ℂ ↥W₀ * Module.finrank (↥Qbar) ↥(X₀ ⊓ W.restrictScalars (↥Qbar)) ≤
        Module.finrank (↥Qbar) ↥X₀ * Module.finrank ℂ ↥W)
    (hdn : Module.finrank ℂ ↥W₀ < Module.finrank (↥Qbar) ↥X₀)
    (hXY : ∀ x ∈ X₀, ∀ y ∈ Y, x ⬝ᵥ y ∈ LogAlgTilde) :
    ∃ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ ∧
      (Module.finrank (↥Qbar) ↥X₀ - Module.finrank ℂ ↥W₀) *
          (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar))) ≤
        Module.finrank (↥Qbar) ↥X₀ * (n - Module.finrank ℂ ↥V) := by
  sorry

end DiazModulus
