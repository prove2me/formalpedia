-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInfty_cwLoop
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInfty_cwLoop
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T14:59:16.856234+00:00
-- url     : https://prove2.me/theorems/d9bf53f6-7a07-44f7-a8fb-bc4580252a62
-- title:
--   Loops near a puncture of nonzero charge converge to a Reeb orbit
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Write $Q(\rho)=\int_0^1 w(\gamma_\rho(t))^*\lambda$ for the action of the clockwise loop $\gamma_\rho(t)=\rho e^{-2\pi i t}$, and call $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$ the gradient bound near the puncture, where $|\nabla u|=\|Da\|+\|Dw\|$ ($\mathbb R$-invariant). Assume the gradient bound near the puncture and $Q(\rho)\to Q\neq0$. Then for every sequence $\rho_k\to0^+$ there are a subsequence $\rho_{k_j}$, a periodic Reeb orbit $(x,|Q|)$ (period $|Q|$) and $c\in\mathbb R$ such that the loops $t\mapsto w(\rho_{k_j}e^{-2\pi i t})$ converge in $C^\infty(\mathbb R)$ to $t\mapsto x(Qt+c)$. (The gradient bound gives $C^\infty_{loc}$-compactness of the shifted cylinders $u(\rho_k e^{-2\pi(s+it)})-a(u(\rho_k))$; the limit has zero $d\lambda$-energy, hence is an orbit cylinder, and its loop action is $Q$.)
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3 (convergence to periodic orbits); C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Theorem 9.8 and its proof, pp. 157-160

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- (d) Nonzero charge: under the gradient bound, along any `ρ_k → 0⁺` a subsequence of the loops
`t ↦ proj(u(ρ_k e^{-2π i t}))` converges in `C^∞` to `t ↦ x(Q t + c)` for a periodic Reeb orbit
`(x, |Q|)`. -/
theorem exists_subseq_tendstoCInfty_cwLoop {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (Q : ℝ) (hQ0 : Q ≠ 0) (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q))
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H, P.T = |Q| ∧ ∃ c : ℝ,
      TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ (φ k)))) (fun t => P.x (Q * t + c)) := by
  sorry

end FiniteEnergyPlane
