-- Prove2me | Theorems.Thm_DQI_Semicircle_lemma_9_1
-- name    : DQI.Semicircle.lemma_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:27.686165+00:00
-- url     : https://prove2.me/theorems/c325e5e1-d2b6-49f8-859d-4c4404908997
-- title:
--   Lemma 9.1, p. 26 — if 2ℓ < d⊥ then ⟨P̃(f)|P̃(f)⟩ = ‖w‖²
-- statement:
--   Let $p$ be prime, $B\in\mathbb F_p^{m\times n}$ with $m>n$, and $|F_i|=r$ for all $i$ with $1\le r\le p-1$. Let $\ell\ge0$ and $\mathbf w\in\mathbb R^{\ell+1}$. If every nonzero codeword of $C^\perp=\{\mathbf d\in\mathbb F_p^m: B^T\mathbf d=0\}$ has Hamming weight greater than $2\ell$ (that is, $2\ell<d^\perp$), then
--   $$\langle\tilde P(f)|\tilde P(f)\rangle=\sum_{\mathbf s\in\mathbb F_p^n}|\tilde P(\mathbf s)|^2=\|\mathbf w\|^2=\sum_{k=0}^\ell w_k^2 .$$
--
--   Together with the unitarity of the Fourier transform this shows that $\sum_kw_k|P^{(k)}\rangle$ is normalized exactly when $\mathbf w$ is a unit vector.
--
--   **Formalization Note** $m>n$ is the paper's standing assumption; it guarantees a nonzero codeword, so the distance condition forces $2\ell<m$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 26, Lemma 9.1

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- Lemma 9.1, p. 26: if `2ℓ < d^⊥` then `⟨P̃(f)|P̃(f)⟩ = ‖w‖²`. -/
theorem lemma_9_1 (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) (hdist : DistGt B (2 * ℓ)) :
    ∑ s : Fin n → ZMod p, ‖Ptilde B F ℓ w s‖ ^ 2 = ∑ k, w k ^ 2 := by sorry

end DQI.Semicircle
