-- Prove2me | Theorems.Thm_DiazModulus_fv_gram_zero_block
-- name    : DiazModulus.fv_gram_zero_block
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:31.685329+00:00
-- url     : https://prove2.me/theorems/858f5f0a-25e9-4028-a3e5-3d4153a0caeb
-- title:
--   Roy's Corollary 1 for a Gram matrix: if X · Y ⊆ ℒ̃ and X ≠ 0, there are X₁ ⊆ X, Y₁ ⊆ Y with X₁ ≠ 0, X₁ · Y₁ = 0 and dℓ′ ≤ r(dim X₁ + ℓ′), d = dim X, ℓ′ = dim Y − dim Y₁, r = dim_ℂ span_ℂ X
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $u, v \in \mathbb C^n$, $u \cdot v = \sum_k u_k v_k$ is the bilinear dot product (not the Hermitian one). For a $\overline{\mathbb Q}$-subspace $X$ and a $\mathbb C$-subspace $W$ of $\mathbb C^n$, $X \cap W$ is a $\overline{\mathbb Q}$-subspace; dimensions are over $\overline{\mathbb Q}$ for $\overline{\mathbb Q}$-subspaces and over $\mathbb C$ for $\mathbb C$-subspaces.
--
--   Let $X, Y \subseteq \mathbb C^n$ be finite-dimensional $\overline{\mathbb Q}$-subspaces with $d = \dim_{\overline{\mathbb Q}} X \ge 1$ and $x \cdot y \in \widetilde{\mathcal L}$ for all $x \in X$ and $y \in Y$. Then there are $\overline{\mathbb Q}$-subspaces $X_1 \subseteq X$ and $Y_1 \subseteq Y$ with $d' = \dim_{\overline{\mathbb Q}} X_1 \ge 1$ and $x \cdot y = 0$ for all $x \in X_1$, $y \in Y_1$, such that, with $\ell' = \dim_{\overline{\mathbb Q}} Y - \dim_{\overline{\mathbb Q}} Y_1$ and $r = \dim_{\mathbb C} \mathrm{span}_{\mathbb C} X$,
--   $$d\,\ell' \le r\,(d' + \ell').$$
-- source:
--   Step of the proof of M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Th. 2.1 (p. 6): Roy's Corollary 1 (Roy 1992, Cor. 1; DALAG, Th. 12.20, p. 435), proved on the platform as DiazModulus.roy_rank_bound, applied to the Gram matrix (xᵢ · yⱼ) of bases of X and Y. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_gram_zero_block {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X] [FiniteDimensional (↥Qbar) ↥Y]
    (hX : 0 < Module.finrank (↥Qbar) ↥X)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x ⬝ᵥ y ∈ LogAlgTilde) :
    ∃ X₁ Y₁ : Submodule (↥Qbar) (Fin n → ℂ), X₁ ≤ X ∧ Y₁ ≤ Y ∧
      0 < Module.finrank (↥Qbar) ↥X₁ ∧ (∀ x ∈ X₁, ∀ y ∈ Y₁, x ⬝ᵥ y = 0) ∧
      Module.finrank (↥Qbar) ↥X * (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥Y₁) ≤
        Module.finrank ℂ ↥(Submodule.span ℂ (X : Set (Fin n → ℂ))) *
          (Module.finrank (↥Qbar) ↥X₁ + (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥Y₁)) := by
  sorry

end DiazModulus
