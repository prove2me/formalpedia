-- Prove2me | Theorems.Thm_DCPenalty_Penalty_eq_3_10
-- name    : DCPenalty.Penalty.eq_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:32.66348+00:00
-- url     : https://prove2.me/theorems/b1435c7a-8f33-470c-8cf5-8cf71b9cd737
-- title:
--   (3.10), pp. 9–10 — along a convergent subsequence of a penalty run, F_{ρ_k}(x^k) − η_k ≤ Q_{ρ_k}(x; x^k, j₀, J) for the active j₀, J
-- statement:
--   Let $\{x^k\}$ be a run of Algorithm 3.1 (with $\rho_k=\rho_0\sigma^k$) and let the subsequence $\{x^k\}_{k\in\mathcal K}$ converge to $x^\infty$. Then for all sufficiently large $k\in\mathcal K$,
--
--   $$
--   \phi_0(x^k)+\zeta_0(x^k)-\psi_0(x^k)+\rho_k\sum_{i=1}^I[\phi_i(x^k)+\zeta_i(x^k)-\psi_i(x^k)]_+^p-\eta_k\ \le\ Q_{\rho_k}(x;x^k,j_0,\mathbb J)
--   $$
--
--   for all $j_0\in\mathcal J_0(x^\infty)$, all $\mathbb J\in\mathcal J(x^\infty)$ and all $x\in X$; here the left side is $F_{\rho_k}(x^k)-\eta_k$.
--
--   This inequality, which no longer refers to the $\epsilon$-active sets at $x^k$, is the starting point of every part of the proof of Theorem 3.1.
--
--   **Formalization Note** The subsequence is a strictly increasing $K:\mathbb N\to\mathbb N$; "for $k\in\mathcal K$ sufficiently large" is "eventually in $k$" for the iterate $x^{K(k)}$, with penalty parameter $\rho_0\sigma^{K(k)}$ and tolerance $\eta_{K(k)}$.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, pp. 9–10, proof of Theorem 3.1, (3.10)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

open Filter Topology

/-- (3.10), pp. 9–10: along a convergent subsequence `{x^k}_{k ∈ 𝒦} → x^∞` of a run of
Algorithm 3.1, for all large `k ∈ 𝒦`,
`F_{ρ_k}(x^k) − η_k ≤ Q_{ρ_k}(x; x^k, j_0, 𝕁)` for all `j_0 ∈ 𝓙_0(x^∞)`, `𝕁 ∈ 𝓙(x^∞)`, `x ∈ X`
(the subsequence is `k ↦ K k`, with `ρ_{K k} = ρ_0 σ^{K k}`). -/
theorem eq_3_10 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {p ε ρ0 σ : ℝ} {η : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : P.IsPenaltyRun p ε ρ0 σ η x)
    {K : ℕ → ℕ} (hK : StrictMono K) {xinf : EuclideanSpace ℝ (Fin n)}
    (hlim : Tendsto (x ∘ K) atTop (𝓝 xinf)) :
    ∀ᶠ k in atTop, ∀ j0 ∈ P.Jact 0 xinf, ∀ jj ∈ P.Jtup xinf, ∀ y ∈ P.X,
      P.Frho p (ρ0 * σ ^ (K k)) (x (K k)) - η (K k) ≤
        P.Qrho p (ρ0 * σ ^ (K k)) (x (K k)) j0 jj y := by sorry

end DCPenalty.Penalty
