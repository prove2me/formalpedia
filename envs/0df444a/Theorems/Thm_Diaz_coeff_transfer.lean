-- Prove2me | Theorems.Thm_Diaz_coeff_transfer
-- name    : Diaz.coeff_transfer
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:32.663058+00:00
-- url     : https://prove2.me/theorems/bac62a30-f42b-4778-8292-8f29ffd43755
-- title:
--   A ring homomorphism fixing $K$ carries bilinear coefficients to those of the transported matrix
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and $\Phi : \mathbb{C} \to \mathbb{C}$ a ring homomorphism fixing $K$ pointwise. Let $M$ be an $m \times n$ complex matrix and let $w \in \mathbb{C}^{m}$, $v \in \mathbb{C}^{n}$ have all entries in $K$. Then
--
--   $$\Phi\!\left(\sum_{i}\sum_{j} w_i\,M_{ij}\,v_j\right)  =  \sum_{i}\sum_{j} w_i\,\Phi(M_{ij})\,v_j .$$
--
--   **Why.** $\Phi$ is additive and multiplicative, so it passes through the double sum and each product; the entries $w_i, v_j$ lie in $K$ and are therefore fixed.
--
--   **Role.** This is the transfer principle for the *third* of the three kinds of data the closure theorem is about — ranks, structural ranks over $K$, and vanishing of matrix coefficients. Combined with `Diaz.Hmat_transfer`, which identifies the transported matrix of a candidate as the matrix of its image, it says that a coefficient over $K$ vanishes for a candidate exactly when it vanishes for the ordinary point it is carried to. Any assertion built from these data therefore transfers, which is what "*a candidate and a model point are indistinguishable*" means precisely.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Transfer.lean#L68-L79

import Mathlib

open ComplexConjugate
variable {K : Subfield ℂ} {u t : ℂ}

theorem Diaz.coeff_transfer (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (w : Fin m → ℂ) (v : Fin n → ℂ)
    (hw : ∀ i, w i ∈ K) (hv : ∀ j, v j ∈ K) :
    Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * (Φ (M i j)) * v j := by sorry
