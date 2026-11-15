-- Prove2me | Theorems.Thm_DiazModulus_fv_theorem_2_1
-- name    : DiazModulus.fv_theorem_2_1
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:46.248866+00:00
-- url     : https://prove2.me/theorems/4f3a4055-9171-4704-b424-2f7839f73786
-- title:
--   Waldschmidt 2005 (Further variations), Th. 2.1, for finite-dimensional Y: if dim_Q̄ X = d > n and μ(Y, ℂⁿ) > d/(d − n), then x · y ∉ ℒ̃ for some x ∈ X, y ∈ Y
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $u, v \in \mathbb C^n$, $u \cdot v = \sum_k u_k v_k$ is the bilinear dot product (not the Hermitian one). For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   For a finite-dimensional $\overline{\mathbb Q}$-subspace $Y \subseteq \mathbb C^n$ with $n \ge 1$, $\mu(Y, \mathbb C^n)$ is the minimum of $\big(\dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap V)\big)/(n - \dim_{\mathbb C} V)$ over the $\mathbb C$-subspaces $V \ne \mathbb C^n$ (Further variations, p. 4); the ratio takes finitely many values, so the minimum is attained.
--
--   Let $X, Y \subseteq \mathbb C^n$ be finite-dimensional $\overline{\mathbb Q}$-subspaces with $d = \dim_{\overline{\mathbb Q}} X > n$, and assume that for every $\mathbb C$-subspace $V \ne \mathbb C^n$
--   $$d\,(n - \dim_{\mathbb C} V) < (d - n)\big(\dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}}(Y \cap V)\big),$$
--   that is, $\mu(Y, \mathbb C^n) > d/(d - n)$. Then $x \cdot y \notin \widetilde{\mathcal L}$ for some $x \in X$ and $y \in Y$.
-- source:
--   M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5; proof pp. 5–6). Stated here for finite-dimensional Y, as the printed proof covers; Further variations states it for every Q̄-subspace Y. The proof replaces the reduction of Further variations (p. 5, after M. Waldschmidt, Transcendance et exponentielles en plusieurs variables, Invent. Math. 63 (1981), 97–127, Lemmes 5.1–5.2) and inequality (2.3) by one ℂ-subspace of maximal slope for X and a relative form of the semistable case, and uses Roy's Corollary 1 once (Roy 1992, Cor. 1; DALAG, Th. 12.20, p. 435; proved on the platform as DiazModulus.roy_rank_bound). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_theorem_2_1 {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X] [FiniteDimensional (↥Qbar) ↥Y]
    (hdn : n < Module.finrank (↥Qbar) ↥X)
    (hμ : ∀ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ →
      Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) <
        (Module.finrank (↥Qbar) ↥X - n) *
          (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar)))) :
    ∃ x ∈ X, ∃ y ∈ Y, x ⬝ᵥ y ∉ LogAlgTilde := by
  sorry

end DiazModulus
