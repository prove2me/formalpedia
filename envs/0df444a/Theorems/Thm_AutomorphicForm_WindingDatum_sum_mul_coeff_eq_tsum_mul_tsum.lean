-- Prove2me | Theorems.Thm_AutomorphicForm_WindingDatum_sum_mul_coeff_eq_tsum_mul_tsum
-- name    : AutomorphicForm.WindingDatum.sum_mul_coeff_eq_tsum_mul_tsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/7bb93060-e5b0-5b94-a568-5174b70f69e1
-- title:
--   Pairing a finitely supported array against winding-datum coefficients
-- statement:
--   Fix naturals $r,d,c$ and a winding datum $\mathcal{D}$ of signature $(r,d,c)$, i.e. a discrete subgroup $\Lambda \le \mathbb{R}^r \times \mathbb{Z}^d$ together with a linear functional $s$ on $\mathbb{R}^r$, a nonzero $\omega \in \mathbb{R}^d$ with $s(x_1) = \sum_i \omega_i (x_2)_i$ for $x \in \Lambda$, a homomorphism $\chi \colon \Lambda \to (\mathbb{R}/\mathbb{Z})^c$, subgroups $\mathcal{D}.\mathrm{sub}\,i \le \Lambda$, continuous integrable windows $\Psi_i$ on $\mathbb{R}^r$ with $\|\Psi_i(x)\| \le C_i \prod_k (1+|x_k|)^{-2}$ and the same bound for their Fourier transforms, integer exponents $m_{i,j}$, phases $\theta_{0,i,j} \in \mathbb{R}/\mathbb{Z}$, shifts $x_{0,i} \in \mathbb{R}^r$ and $n_{0,i} \in \mathbb{Z}^d$, and weights $\lambda_i$. Let $B \subseteq \mathbb{Z}^d$ be finite and $G \colon \mathbb{Z}^d \to \mathbb{C}$ vanish off $B$. Write $T_i(\gamma) = G(\gamma_2 + n_{0,i})\,\Psi_i(x_{0,i} + \gamma_1) \prod_j \mathrm{fourier}(m_{i,j})(\theta_{0,i,j} + \chi(\gamma)_j)$ for $\gamma \in \mathcal{D}.\mathrm{sub}\,i$, viewed in $\Lambda$ via $\mathrm{sub}\,i \le \Lambda$. The assertion is threefold: for each $i$ the family $\gamma \mapsto \|T_i(\gamma)\|$ is summable over $\mathcal{D}.\mathrm{sub}\,i$; the family $i \mapsto \|\lambda_i \sum'_{\gamma} T_i(\gamma)\|$ is summable over $\mathbb{N}$; and $\sum_{n \in B} G(n)\,\mathcal{D}.\mathrm{coeff}(n) = \sum'_i \lambda_i \sum'_{\gamma \in \mathcal{D}.\mathrm{sub}\,i} T_i(\gamma)$, where $\mathcal{D}.\mathrm{coeff}(n) = \sum'_i \lambda_i \sum'_{\gamma \in \mathcal{D}.\mathrm{sub}\,i} \mathcal{D}.\mathrm{fibreTerm}\,i\,n\,\gamma$.
--
--   This is the interface lemma by which a finitely supported array on $\mathbb{Z}^d$ is paired with the coefficient array of a winding datum: the pairing is rewritten as an absolutely convergent weighted sum over the lattice points of the windows times the twisting characters, with no indicator left. It is used in the comparison of the geometric terms along Hecke words, being cited by the two results on class sums and orbital integrals expressed through winding data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindingDatum_sum_mul_coeff_eq_tsum_mul_tsum.lean

import Mathlib
import Definitions.Def_AutomorphicForm_WindingDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.WindingDatum.sum_mul_coeff_eq_tsum_mul_tsum
    {r d c : ℕ} (𝒟 : AutomorphicForm.WindingDatum r d c) (B : Finset (Fin d → ℤ)) (G : (Fin d → ℤ) → ℂ)
    (hG : ∀ n ∉ B, G n = 0) :
    (∀ i : ℕ, Summable fun γ : 𝒟.sub i =>
        ‖G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j))‖) ∧
    (Summable fun i : ℕ => ‖𝒟.lam i * ∑' γ : 𝒟.sub i,
        G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j))‖) ∧
    ∑ n ∈ B, G n * 𝒟.coeff n = ∑' i : ℕ, 𝒟.lam i * ∑' γ : 𝒟.sub i,
        G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j)) := by sorry
