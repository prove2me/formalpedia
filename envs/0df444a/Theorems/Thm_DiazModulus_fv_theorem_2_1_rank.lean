-- Prove2me | Theorems.Thm_DiazModulus_fv_theorem_2_1_rank
-- name    : DiazModulus.fv_theorem_2_1_rank
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:48.302017+00:00
-- url     : https://prove2.me/theorems/e4db0982-f503-44a4-b431-c32603b2d4fa
-- title:
--   Waldschmidt 2005 (Further variations), Th. 2.1: for Q̄-subspaces X, Y of ℂⁿ, Y of any dimension, if dim_Q̄ X = d > n and μ(Y, ℂⁿ) > d/(d − n), then x · y ∉ ℒ̃ for some x ∈ X, y ∈ Y
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $u, v \in \mathbb C^n$, $u \cdot v = \sum_k u_k v_k$ is the bilinear dot product (not the Hermitian one). For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   For a $\overline{\mathbb Q}$-subspace $Y \subseteq \mathbb C^n$ of any dimension, with $n \ge 1$, $\mu(Y, \mathbb C^n)$ is the minimum of $\dim_{\overline{\mathbb Q}}\big(Y/(Y \cap V)\big)/(n - \dim_{\mathbb C} V)$ over the $\mathbb C$-subspaces $V \ne \mathbb C^n$ (Further variations, p. 4), an infinite dimension giving the value $\infty$; the minimum is attained. For finite-dimensional $Y$ the numerator is $\dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap V)$.
--
--   Let $X, Y \subseteq \mathbb C^n$ be $\overline{\mathbb Q}$-subspaces, $X$ finite-dimensional with $d = \dim_{\overline{\mathbb Q}} X > n$, and $Y$ of any dimension. For a $\mathbb C$-subspace $V$ let $\kappa(V) = \dim_{\overline{\mathbb Q}}\big(Y/(Y \cap V)\big)$, the dimension of the quotient as a cardinal, as in the printed definition of $\mu$. Assume that for every $\mathbb C$-subspace $V \ne \mathbb C^n$, in cardinal arithmetic,
--   $$d\,(n - \dim_{\mathbb C} V) < (d - n)\,\kappa(V),$$
--   that is, $\mu(Y, \mathbb C^n) > d/(d - n)$ (when $\kappa(V)$ is infinite the inequality holds at $V$, since $d - n \ge 1$). Then $x \cdot y \notin \widetilde{\mathcal L}$ for some $x \in X$ and $y \in Y$.
-- source:
--   M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5; proof pp. 5–6), as printed: for every Q̄-subspace Y, with the dimension of Y/(Y ∩ V) over Q̄ taken as a cardinal, as in the definition of μ(Y, ℂⁿ) (p. 4). Proved from the finite-witness form DiazModulus.fv_theorem_2_1_general, where the general case is reduced to the finite-dimensional one, and DiazModulus.fv_rank_quot_witness. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_theorem_2_1_rank {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X]
    (hdn : n < Module.finrank (↥Qbar) ↥X)
    (hμ : ∀ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ →
      ((Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) : ℕ) : Cardinal) <
        ((Module.finrank (↥Qbar) ↥X - n : ℕ) : Cardinal) *
          Module.rank (↥Qbar) (↥Y ⧸ (V.restrictScalars (↥Qbar)).comap Y.subtype)) :
    ∃ x ∈ X, ∃ y ∈ Y, x ⬝ᵥ y ∉ LogAlgTilde := by
  sorry

end DiazModulus
