-- Prove2me | Theorems.Thm_DCPenalty_Penalty_eq_3_26
-- name    : DCPenalty.Penalty.eq_3_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:24.102893+00:00
-- url     : https://prove2.me/theorems/b200c41e-d534-4873-ae51-fa9501236d48
-- title:
--   (3.26), p. 12 — x^∞ minimizes the convex model ĥ_{0,j₀} over Y_J(x^∞)
-- statement:
--   Let $\{x^k\}$ be a run of Algorithm 3.1 and let $\{x^k\}_{k\in\mathcal K}$ converge to $x^\infty$. Suppose $x^\infty\in\Omega$, $\mathcal I_=(x^\infty)\neq\emptyset$ and the PSCQ holds for $\Omega$ at $x^\infty$. Then for every $\mathbb J\in\mathcal J(x^\infty)$ and every $j_0\in\mathcal J_0(x^\infty)$,
--
--   $$
--   x^\infty\in\operatorname*{Argmin}_{x\in Y_{\mathbb J}(x^\infty)}\ \hat h_{0,j_0}(x),\qquad \hat h_{0,j_0}(x)=\hat\phi_0(x;x^\infty)+\zeta_0(x)-\ell_{\psi_{0,j_0}}(x;x^\infty),
--   $$
--
--   that is, $x^\infty\in Y_{\mathbb J}(x^\infty)$ and $\hat h_{0,j_0}(x^\infty)\le\hat h_{0,j_0}(x)$ for all $x\in Y_{\mathbb J}(x^\infty)$.
--
--   From this minimality the paper reads off $F'(x^\infty;d)\ge 0$ on each cone $\mathcal T_{Y_{\mathbb J}(x^\infty)}(x^\infty)$, and Theorem 2.1 then gives B-stationarity.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 12, proof of Theorem 3.1(iii), (3.26)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

open Filter Topology

/-- (3.26), p. 12: under the hypotheses of Theorem 3.1(iii), for every `𝕁 ∈ 𝓙(x^∞)` and
`j_0 ∈ 𝓙_0(x^∞)`, `x^∞ ∈ Argmin_{x ∈ Y_𝕁(x^∞)} ĥ_{0,j_0}(x)`, where
`ĥ_{0,j_0}(x) = φ̂_0(x; x^∞) + ζ_0(x) − ℓ_{ψ_{0,j_0}}(x; x^∞)`. -/
theorem eq_3_26 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {p ε ρ0 σ : ℝ} {η : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : P.IsPenaltyRun p ε ρ0 σ η x)
    {K : ℕ → ℕ} (hK : StrictMono K) {xinf : EuclideanSpace ℝ (Fin n)}
    (hlim : Tendsto (x ∘ K) atTop (𝓝 xinf))
    (hfeas : xinf ∈ P.Ω) (hact : (P.Ieq xinf).Nonempty) (hpscq : P.PSCQ xinf) :
    ∀ jj ∈ P.Jtup xinf, ∀ j0 ∈ P.Jact 0 xinf,
      xinf ∈ P.Y jj xinf ∧ ∀ y ∈ P.Y jj xinf,
        P.phiHat 0 xinf xinf + P.ζ 0 xinf - lin (P.ψ 0 j0) xinf xinf ≤
          P.phiHat 0 xinf y + P.ζ 0 y - lin (P.ψ 0 j0) xinf y := by sorry

end DCPenalty.Penalty
