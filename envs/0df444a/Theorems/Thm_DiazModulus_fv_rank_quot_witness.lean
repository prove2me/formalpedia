-- Prove2me | Theorems.Thm_DiazModulus_fv_rank_quot_witness
-- name    : DiazModulus.fv_rank_quot_witness
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:40.608199+00:00
-- url     : https://prove2.me/theorems/73a0cf37-4ede-4a4d-832d-dafc99781172
-- title:
--   For a Q̄-subspace Y and a ℂ-subspace V of ℂⁿ, if the Q̄-dimension of Y/(Y ∩ V), a cardinal, is at least N ∈ ℕ, some finite-dimensional Y₀ ⊆ Y has dim_Q̄ Y₀ − dim_Q̄(Y₀ ∩ V) ≥ N
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   Let $Y \subseteq \mathbb C^n$ be a $\overline{\mathbb Q}$-subspace of any dimension, $V \subseteq \mathbb C^n$ a $\mathbb C$-subspace and $N$ a natural number, and assume that the quotient $Y/(Y \cap V)$ has dimension at least $N$ over $\overline{\mathbb Q}$, the dimension being taken as a cardinal. Then there is a finite-dimensional $\overline{\mathbb Q}$-subspace $Y_0 \subseteq Y$ with
--   $$\dim_{\overline{\mathbb Q}} Y_0 - \dim_{\overline{\mathbb Q}}(Y_0 \cap V) \ge N.$$
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 5), for every Q̄-subspace Y, in the printed form of the hypothesis: finite-dimensional witnesses for a lower bound on the dimension of Y/(Y ∩ V) (Further variations, p. 4), taken as a cardinal. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_rank_quot_witness {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ))
    (V : Submodule ℂ (Fin n → ℂ)) (N : ℕ)
    (hN : (N : Cardinal) ≤
      Module.rank (↥Qbar) (↥Y ⧸ (V.restrictScalars (↥Qbar)).comap Y.subtype)) :
    ∃ Y₀ : Submodule (↥Qbar) (Fin n → ℂ), Y₀ ≤ Y ∧ FiniteDimensional (↥Qbar) ↥Y₀ ∧
      N ≤ Module.finrank (↥Qbar) ↥Y₀ - Module.finrank (↥Qbar) ↥(Y₀ ⊓ V.restrictScalars (↥Qbar)) := by
  sorry

end DiazModulus
