-- Prove2me | Theorems.Thm_BetheKS_appF_frobenius_bound
-- name    : BetheKS.appF_frobenius_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:24.565379+00:00
-- url     : https://prove2.me/theorems/6398e3d0-c960-4cbb-84e5-b5e8bb6dfa04
-- title:
--   App. F, p.27 — $\|C_n\|_F^2\ge\pi_{\min}\sum_{i\ge2,|\mu_i|>\sqrt d}\|U_n^{\mathsf T}X_i/\sqrt n\|_2^2$
-- statement:
--   Let $(\mu_i,\phi_i)$ be a planted eigenbasis, $\sigma:[n]\to[r]$ a labeling with exact community sizes, $X_i=\phi_i\circ\sigma$, and $U_1,\dots,U_m\in\mathbb R^n$ orthonormal and orthogonal to $\mathbf 1$. With $x_u:=\sqrt n\,(U_1(u),\dots,U_m(u))^{\mathsf T}$ and
--   $$
--   C_n=\frac1n\sum_u(e_{\sigma(u)}-\pi)x_u^{\mathsf T}\in\mathbb R^{r\times m},
--   $$
--   orthonormality of the planted eigenfunctions gives
--   $$
--   \|C_n\|_F^2\ \ge\ \pi_{\min}\sum_{i\ge2,\ |\mu_i|>\sqrt d}\Big\|U_n^{\mathsf T}\frac{X_i}{\sqrt n}\Big\|_2^2 .
--   $$
--   This deterministic inequality turns the spectral correlation of App. F's joint-limit step into a lower bound on the confusion matrix of the rounding.
--
--   **Formalization Note** $C_n$ is written entrywise; $\|U_n^{\mathsf T}X_i/\sqrt n\|_2^2=\sum_k(\langle U_k,X_i\rangle/\sqrt n)^2$.
--
--   Differences from the source:
--
--   - generalization: U_n an orthonormal basis of E_n ∩ 1^⊥ (with m columns) → any orthonormal family U_1,…,U_m orthogonal to 1, of any size m; reason: the inequality uses only U ⊥ 1; the paper's U_n is such a family
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), App. F, proof of Theorem 2.3, p.27 (PDF p.28), display "Orthonormality of the planted eigenfunctions gives"

import Mathlib
import Definitions.Def_BetheKS_outlierSpace

set_option autoImplicit false

namespace BetheKS

/-- **App. F, proof of Theorem 2.3 (lower bound on `‖Cₙ‖_F`)** — Dong, McKenzie, arXiv:2610.41802 (held
version, sha256 4da41e16…), p.27 (PDF p.28): with `xᵤ := √n Uₙ(u,·)ᵀ` and
`Cₙ = (1/n) ∑ᵤ (e_{σ(u)} − π) xᵤᵀ`, "Orthonormality of the planted eigenfunctions gives
`‖Cₙ‖²_F ≥ π_min ∑_{i≥2, |µᵢ|>√d} ‖Uₙᵀ Xᵢ/√n‖²₂`."

Deterministic: for every `n`, every exact-size labeling `σ`, and every family `U₁,…,U_m` of
orthonormal vectors orthogonal to `1`.

**Formalization Note.** `Cₙ` is written entrywise, `(Cₙ)_{a,k} = (1/n) ∑ᵤ (1{σ(u)=a} − π_a) √n U_k(u)`.
The paper's `Uₙ` is an orthonormal basis of `Eₙ ∩ 1^⊥`; the inequality is stated for every
orthonormal family orthogonal to `1`, of any size `m`. -/
theorem appF_frobenius_bound {r : ℕ} (p : SBMParams r)
    (μ : Fin r → ℝ) (ϕ : Fin r → Fin r → ℝ) (hϕ : IsPlantedEigenbasis p μ ϕ)
    {n : ℕ} (σ : Fin n → Fin r) (hσ : IsExactSize p σ)
    {m : ℕ} (U : Fin m → EuclideanSpace ℝ (Fin n)) (hU : Orthonormal ℝ U)
    (hU1 : ∀ k, inner ℝ (U k) (onesVec n) = 0) :
    piMin p * ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val ≠ 0 ∧ Real.sqrt p.d < |μ i|),
        ∑ k, (inner ℝ (U k) (WithLp.toLp 2 (ϕ i ∘ σ)) / Real.sqrt n) ^ 2 ≤
      ∑ a : Fin r, ∑ k : Fin m,
        ((1 / (n : ℝ)) * ∑ u, ((if σ u = a then (1 : ℝ) else 0) - p.pi a) * (Real.sqrt n * U k u)) ^ 2 := by sorry

end BetheKS
