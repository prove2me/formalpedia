-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_theorem_3_1
-- name    : DeFinettiSDP.Hierarchy.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:14.146945+00:00
-- url     : https://prove2.me/theorems/660ed891-cb15-4ed1-8541-c0635ff1da05
-- title:
--   Theorem 3.1, p. 11 — Q ≤ SDPₙ ≤ Q + ‖G‖∞·d_B²(d_B+1)·√((2 ln 2) log d_A/n), and Q = lim SDPₙ
-- statement:
--   Let $Q$ be the optimal value of the constrained bilinear program
--
--   $$Q=\max\ \mathrm{Tr}[G_{AB}(W_A\otimes W_B)]\quad\text{s.t. } W_A\succeq0,\ W_B\succeq0,\ \mathrm{Tr}W_A=\mathrm{Tr}W_B=1,\ \Lambda_{A\to C_A}(W_A)=X_{C_A},\ \Gamma_{B\to C_B}(W_B)=Y_{C_B},$$
--
--   for $G_{AB}\in\mathcal S_A\otimes\mathcal S_B$, linear maps $\Lambda_{A\to C_A}$, $\Gamma_{B\to C_B}$ and matrices $X_{C_A}$, $Y_{C_B}$, and let $\mathrm{SDP}_n$ be the optimal value of the semidefinite program
--
--   $$\mathrm{SDP}_n=\max\ \mathrm{Tr}[G_{AB}W_{AB_1}]\quad\text{s.t. } W_{AB_1^n}\succeq0,\ \mathrm{Tr}W_{AB_1^n}=1,\ W_{AB_1^n}=\mathcal U^\pi_{B_1^n}(W_{AB_1^n})\ \forall\pi\in\mathfrak S_n,$$
--   $$\Lambda_{A\to C_A}(W_{AB_1^n})=X_{C_A}\otimes W_{B_1^n},\qquad\Gamma_{B_n\to C_B}(W_{B_1^n})=W_{B_1^{n-1}}\otimes Y_{C_B}.$$
--
--   Then for every $n\ge1$,
--
--   $$0\ \le\ \mathrm{SDP}_n-Q\ \le\ \|G_{AB}\|_\infty\, d_B^2(d_B+1)\sqrt{\frac{(2\ln2)\log d_A}{n}},$$
--
--   with $\log$ base 2, and consequently $Q=\lim_{n\to\infty}\mathrm{SDP}_n$.
--
--   The hierarchy gives certified outer bounds on a nonconvex bilinear program that converge to its optimum at rate $O(1/\sqrt n)$, with the constraints handled exactly at every level.
--
--   **Formalization Note** The page states $0\le\mathrm{SDP}_n-Q\le\mathrm{poly}(d)/\sqrt n$ with $d=\max\{d_A,d_B\}$. The rate stated here is the one the paper's proof gives: $\|G_{AB}\|_\infty$ (the Hölder step, p. 11) times the de Finetti error of Theorem 2.3, $\min\{f(A,B),f(B|\cdot)\}\sqrt{(2\ln2)\log d_A/n}$, with the minimum bounded by $d_B^2(d_B+1)$ (p. 6 and Lemma D.1). Since $\|G\|_\infty$ is not a function of $d$, "poly$(d)$" is read as "$\|G\|_\infty\cdot$poly$(d)$". The objective is the real part of $\mathrm{Tr}[G\,W]$ (equal to it for Hermitian $G$). `SDPval … n` is the page's $\mathrm{SDP}_{n+1}$, so the bound has denominator $n+1$. No feasibility hypothesis is assumed: the feasible sets of $Q$ and of every level are empty together, and then all values are $0$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, Theorem 3.1 and its proof, p. 11 (rate from Theorem 2.3, p. 7, and f(B|·) ≤ d_B²(d_B+1), p. 6)

import Mathlib
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems
import Definitions.Def_DeFinettiSDP_Hierarchy_Problem
open Matrix
open scoped Kronecker ComplexOrder

namespace DeFinettiSDP.Hierarchy

/-- **Theorem 3.1** (arXiv:1810.12197v3, p. 11), with the explicit rate of its proof. For the
constrained bilinear program `Q` and its SDP hierarchy (`SDPval … n` is the page's `SDP_{n+1}`,
with `n + 1` copies of `B`), for every `n`,
`Q ≤ SDP_{n+1} ≤ Q + ‖G‖_∞ · d_B²(d_B + 1) · √((2 ln 2) log₂ d_A / (n + 1))`,
and consequently `SDP_{n+1} → Q` as `n → ∞`. -/
theorem theorem_3_1 {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) :
    (∀ n : ℕ, Qval G Λ Γ X Y ≤ SDPval G Λ Γ X Y n ∧
      SDPval G Λ Γ X Y n ≤ Qval G Λ Γ X Y +
        opNormInf G * ((dB : ℝ) ^ 2 * ((dB : ℝ) + 1)) *
          Real.sqrt (2 * Real.log 2 * Real.logb 2 (dA : ℝ) / ((n : ℝ) + 1))) ∧
    Filter.Tendsto (fun n : ℕ => SDPval G Λ Γ X Y n) Filter.atTop (nhds (Qval G Λ Γ X Y)) := by sorry

end DeFinettiSDP.Hierarchy
