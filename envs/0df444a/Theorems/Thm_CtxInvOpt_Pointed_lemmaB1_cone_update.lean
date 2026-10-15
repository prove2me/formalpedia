-- Prove2me | Theorems.Thm_CtxInvOpt_Pointed_lemmaB1_cone_update
-- name    : CtxInvOpt.Pointed.lemmaB1_cone_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:27.072656+00:00
-- url     : https://prove2.me/theorems/f4c32e13-334d-477c-b75c-a060aa07c612
-- title:
--   Lemma B-1, App-22, case η = 0 only — ConeUpdate contains the cut cone and shrinks ∏λ_i(W) by e^{−1/2(p−1)}
-- statement:
--   Let $p=m+1\ge 3$, let $W\in\mathbb D^{p-1}_{++}$ be diagonal and positive definite, let $U\in\mathbb R^{p\times p}$ be orthonormal, and let $\delta\in\mathbb R^p$ satisfy $\delta'\hat c(W,U)=\delta'Ue_1\le 0$ and $(U^{-1}\delta)_{[2:p]}\ne 0$. Let $(\widetilde W,\widetilde U)$ be any output of ConeUpdate on $(W,U,\delta)$ with $\eta=0$. Then
--   1. $E(W,U)\cap\{c\in\mathbb R^p:\ \delta'c\ge 0\}\subseteq E(\widetilde W,\widetilde U)$;
--   2. $\widetilde W$ is positive definite;
--   3. the product of the eigenvalues shrinks:
--   $$\prod_{i=1}^{p-1}\lambda_i(\widetilde W)\le e^{-1/(2(p-1))}\prod_{i=1}^{p-1}\lambda_i(W).$$
--
--   This is the cone analogue of the volume decrease of the ellipsoid method, and it is the engine of Lemma 3.
--
--   **Formalization Note** Only the case $\eta=0$ of Lemma B-1 is formalized. For $\eta>0$ the half-space $\{\delta'c\ge-\eta\}$ is not homogeneous, and the printed inclusion fails. The page writes $e^{-1/2(d-1)}$ with $d$ for $p$, and $\sqrt{\bar\delta'W\delta}$ in the denominator of $b$; they are read as $e^{-1/(2(p-1))}$ and $\sqrt{\bar\delta'W\bar\delta}$. The hypothesis $(U^{-1}\delta)_{[2:p]}\ne0$ makes $\bar\delta$ defined, and $p\ge3$ is the range of the $N$ formula, which divides by $(p-1)^2-1$. Positivity of $\widetilde W$ is stated because $\widetilde W\in\mathbb D^{p-1}_{++}$ is implicit in "$E(\widetilde W,\widetilde U)$". The column order of $V$ and the eigenvalue pairing are those fixed in `IsConeUpdate`.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. App-22, Lemma B-1 (η = 0); proof App-23–App-25

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_ConeUpdate

namespace CtxInvOpt.Pointed

open Matrix

/-- **Lemma B-1, App-22, the case `η = 0`.** Let `p = m + 1 ≥ 3`, `W = diag(w) ∈ D^{p−1}_{++}`, `U`
orthonormal, and `δ ∈ ℝ^p` with `δ′ĉ(W, U) = δ′Ue₁ ≤ 0` and `(U⁻¹δ)_{[2:p]} ≠ 0`. For every output
`(W̃, Ũ)` of ConeUpdate on `(W, U, δ)` with `η = 0`,
`E(W, U) ∩ {c : δ′c ≥ 0} ⊆ E(W̃, Ũ)`, `W̃` is positive definite, and
`∏ λ_i(W̃) ≤ e^{−1/(2(p−1))} ∏ λ_i(W)`. -/
theorem lemmaB1_cone_update {m : ℕ} (hm : 2 ≤ m) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ)
    (δ : EuclideanSpace ℝ (Fin (m + 1))) (hδ : inner ℝ δ (axisVec U) ≤ 0)
    (htail : tailVec (rotCoord U δ) ≠ 0)
    (w' : Fin m → ℝ) (U' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hupd : IsConeUpdate w U δ w' U') :
    ellCone w U ∩ {c | 0 ≤ inner ℝ δ c} ⊆ ellCone w' U' ∧
      (∀ i, 0 < w' i) ∧
      ∏ i, w' i ≤ Real.exp (-(1 / (2 * (m : ℝ)))) * ∏ i, w i := by sorry

end CtxInvOpt.Pointed
