-- Prove2me | Theorems.Thm_DiazModulus_fv_max_slope
-- name    : DiazModulus.fv_max_slope
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:40.002231+00:00
-- url     : https://prove2.me/theorems/4a4f3da9-8eb7-414e-9ef2-9a6d23811ec1
-- title:
--   A ℂ-subspace of maximal slope: for a finite-dimensional Q̄-subspace X ⊆ ℂⁿ, n ≥ 1, some ℂ-subspace W₀ ≠ 0 maximises dim_Q̄(X ∩ W)/dim_ℂ W over the ℂ-subspaces W ≠ 0
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $u, v \in \mathbb C^n$, $u \cdot v = \sum_k u_k v_k$ is the bilinear dot product (not the Hermitian one). For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   Let $n \ge 1$ and let $X \subseteq \mathbb C^n$ be a finite-dimensional $\overline{\mathbb Q}$-subspace. Then there is a $\mathbb C$-subspace $W_0 \ne 0$ of $\mathbb C^n$ such that
--   $$\dim_{\overline{\mathbb Q}}(X \cap W)\cdot\dim_{\mathbb C} W_0 \le \dim_{\overline{\mathbb Q}}(X \cap W_0)\cdot\dim_{\mathbb C} W$$
--   for every $\mathbb C$-subspace $W \subseteq \mathbb C^n$; that is, $W_0$ maximises the slope $\dim_{\overline{\mathbb Q}}(X \cap W)/\dim_{\mathbb C} W$ among the $\mathbb C$-subspaces $W \ne 0$.
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (pp. 5–6); the analogue of M. Waldschmidt, Transcendance et exponentielles en plusieurs variables, Invent. Math. 63 (1981), 97–127, Lemme 5.1 (p. 106). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_max_slope {n : ℕ} (hn : 0 < n) (X : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X] :
    ∃ W₀ : Submodule ℂ (Fin n → ℂ), W₀ ≠ ⊥ ∧
      ∀ W : Submodule ℂ (Fin n → ℂ),
        Module.finrank (↥Qbar) ↥(X ⊓ W.restrictScalars (↥Qbar)) * Module.finrank ℂ ↥W₀ ≤
          Module.finrank (↥Qbar) ↥(X ⊓ W₀.restrictScalars (↥Qbar)) * Module.finrank ℂ ↥W := by
  sorry

end DiazModulus
