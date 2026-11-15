-- Prove2me | Theorems.Thm_DiazModulus_fv_theorem_2_1_general
-- name    : DiazModulus.fv_theorem_2_1_general
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:53.683708+00:00
-- url     : https://prove2.me/theorems/09606ca3-0cff-4973-9cc2-244aa8722908
-- title:
--   Waldschmidt 2005 (Further variations), Th. 2.1, finite-witness form: if dim_Q̄ X = d > n and each V ≠ ℂⁿ has a finite-dimensional Y₀ ⊆ Y with d(n − dim V) < (d − n) dim Y₀/(Y₀ ∩ V), some x · y ∉ ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $u, v \in \mathbb C^n$, $u \cdot v = \sum_k u_k v_k$ is the bilinear dot product (not the Hermitian one). For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   For a $\overline{\mathbb Q}$-subspace $Y \subseteq \mathbb C^n$ of any dimension, with $n \ge 1$, $\mu(Y, \mathbb C^n)$ is the minimum of $\dim_{\overline{\mathbb Q}}\big(Y/(Y \cap V)\big)/(n - \dim_{\mathbb C} V)$ over the $\mathbb C$-subspaces $V \ne \mathbb C^n$ (Further variations, p. 4), an infinite dimension giving the value $\infty$; the minimum is attained. For finite-dimensional $Y$ the numerator is $\dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap V)$.
--
--   Let $X, Y \subseteq \mathbb C^n$ be $\overline{\mathbb Q}$-subspaces, $X$ finite-dimensional with $d = \dim_{\overline{\mathbb Q}} X > n$, and $Y$ of any dimension. Assume that for every $\mathbb C$-subspace $V \ne \mathbb C^n$ there is a finite-dimensional $\overline{\mathbb Q}$-subspace $Y_0 \subseteq Y$, which may depend on $V$, with
--   $$d\,(n - \dim_{\mathbb C} V) < (d - n)\big(\dim_{\overline{\mathbb Q}} Y_0 - \dim_{\overline{\mathbb Q}}(Y_0 \cap V)\big).$$
--   Then $x \cdot y \notin \widetilde{\mathcal L}$ for some $x \in X$ and $y \in Y$.
--
--   This hypothesis is a finite-witness form of Waldschmidt's condition $\mu(Y, \mathbb C^n) > d/(d - n)$, and it is equivalent to it. Indeed, for finite-dimensional $Y_0 \subseteq Y$ the number $\dim_{\overline{\mathbb Q}} Y_0 - \dim_{\overline{\mathbb Q}}(Y_0 \cap V)$ is the dimension of $Y_0/(Y_0 \cap V)$, which embeds in $Y/(Y \cap V)$; and $Y/(Y \cap V)$ has dimension at least $N$ exactly when some finite-dimensional $Y_0 \subseteq Y$ has $\dim_{\overline{\mathbb Q}} Y_0 - \dim_{\overline{\mathbb Q}}(Y_0 \cap V) \ge N$. So the hypothesis says that, for every $V \ne \mathbb C^n$, either $Y/(Y \cap V)$ is infinite-dimensional or $d\,(n - \dim_{\mathbb C} V) < (d - n)\dim_{\overline{\mathbb Q}}\big(Y/(Y \cap V)\big)$; as the minimum defining $\mu$ is attained, this is $\mu(Y, \mathbb C^n) > d/(d - n)$.
-- source:
--   M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5; proof pp. 5–6), for every Q̄-subspace Y, with the hypothesis μ(Y, ℂⁿ) > d/(d − n) (μ defined p. 4) in an equivalent finite-witness form. Further variations states Th. 2.1 for every Q̄-subspace Y. Its proof takes a finite basis of Y. Here the general case is reduced to the finite-dimensional one (DiazModulus.fv_theorem_2_1) by one finite-dimensional subspace Y₀ ⊆ Y that works for every V (DiazModulus.fv_finite_approx). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_theorem_2_1_general {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X]
    (hdn : n < Module.finrank (↥Qbar) ↥X)
    (hμ : ∀ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ →
      ∃ Y₀ : Submodule (↥Qbar) (Fin n → ℂ), Y₀ ≤ Y ∧ FiniteDimensional (↥Qbar) ↥Y₀ ∧
        Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) <
          (Module.finrank (↥Qbar) ↥X - n) *
            (Module.finrank (↥Qbar) ↥Y₀ -
              Module.finrank (↥Qbar) ↥(Y₀ ⊓ V.restrictScalars (↥Qbar)))) :
    ∃ x ∈ X, ∃ y ∈ Y, x ⬝ᵥ y ∉ LogAlgTilde := by
  sorry

end DiazModulus
