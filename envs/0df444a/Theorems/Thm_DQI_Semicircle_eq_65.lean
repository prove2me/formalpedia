-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_65
-- name    : DQI.Semicircle.eq_65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:20.853667+00:00
-- url     : https://prove2.me/theorems/2577f406-326a-44b4-92ff-0bf29a126276
-- title:
--   (65), p. 26 — the QFT F^{⊗n} maps Σ_k w_k|P^(k)⟩ to |P̃(f)⟩ = Σ_k (w_k/√C(m,k)) Σ_{|y|=k} g̃(y)|Bᵀy⟩
-- statement:
--   In the setting of §8.2.1, let $\ell\ge0$ and $\mathbf w\in\mathbb R^{\ell+1}$. Let $a_{\mathbf w}(\mathbf x)=\sum_{k=0}^\ell w_kP^{(k)}(g_1(\mathbf b_1\cdot\mathbf x),\dots,g_m(\mathbf b_m\cdot\mathbf x))/\sqrt{p^{n-k}\binom mk}$ be the amplitude of $\sum_kw_k|P^{(k)}\rangle$. Then for every syndrome $\mathbf s\in\mathbb F_p^n$
--   $$\frac1{\sqrt{p^n}}\sum_{\mathbf x\in\mathbb F_p^n}\omega_p^{\mathbf s\cdot\mathbf x}\,a_{\mathbf w}(\mathbf x)=\sum_{k=0}^{\ell}\frac{w_k}{\sqrt{\binom mk}}\sum_{\substack{\mathbf y\in\mathbb F_p^m,\ |\mathbf y|=k\\ B^T\mathbf y=\mathbf s}}\ \prod_{i:\,y_i\neq0}\tilde g_i(y_i).$$
--   That is, the quantum Fourier transform $F^{\otimes n}$, $F_{ij}=\omega_p^{ij}/\sqrt p$, maps the DQI state to $|\tilde P(f)\rangle$.
--
--   This is the bridge from the computational basis, where the objective is measured, to the syndrome basis, where the decoding structure is visible.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 26, (65); derived on p. 22, (46)–(50)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (65), p. 26 (derived in (46)–(50), p. 22): the quantum Fourier transform `F^{⊗n}`,
`F_{ij} = ω_p^{ij}/√p`, maps `Σ_k w_k |P^{(k)}⟩` to `|P̃(f)⟩`. -/
theorem eq_65 (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) (s : Fin n → ZMod p) :
    (1 / (Real.sqrt ((p : ℝ) ^ n) : ℂ)) * ∑ x : Fin n → ZMod p, omega (s ⬝ᵥ x) * (ampl B F ℓ w x : ℂ) =
      Ptilde B F ℓ w s := by sorry

end DQI.Semicircle
