-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_gradNorm_le_near_puncture
-- name    : FiniteEnergyPlane.exists_norm_mul_gradNorm_le_near_puncture
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T14:59:13.487998+00:00
-- url     : https://prove2.me/theorems/23e2ed98-0096-4ed9-8dd2-5f01ef47068c
-- title:
--   Gradient bound near a puncture of a finite-energy curve
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Write $Q(\rho)=\int_0^1 w(\gamma_\rho(t))^*\lambda$ for the action of the clockwise loop $\gamma_\rho(t)=\rho e^{-2\pi i t}$, and call $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$ the gradient bound near the puncture, where $|\nabla u|=\|Da\|+\|Dw\|$ ($\mathbb R$-invariant). Then there are $r>0$ and $C$ with $|z|\,|\nabla u(z)|\le C$ for all $0<|z|<r$. Otherwise there are $z_k\to0$ with $|z_k|\,|\nabla u(z_k)|\to\infty$; rescaling $u_k(\zeta)=u(|z_k|\zeta)$ on $0<|\zeta|<1/|z_k|$ and bubbling off near $\zeta_k=z_k/|z_k|$ (Hofer's lemma) gives a nonconstant finite-energy plane $v$ whose $d\lambda$-energy on each disc $B_\rho(0)$ is bounded by the liminf of the $d\lambda$-energies of $u$ on discs contained in $B_{2|z_k|}(0)\setminus\{0\}$. These tend to $0$ because $\int_{\dot D}w^*d\lambda\le E(u)<\infty$, so $\int_{\mathbb C}v^*d\lambda=0$, contradicting the positivity of the $d\lambda$-energy of nonconstant finite-energy planes.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3 (gradient bound near punctures, via bubbling off); C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Theorem 9.8 and its proof, pp. 157-160

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- (b) Gradient bound near a puncture: `|z| · |∇u(z)| ≤ C` near `0` (bubbling off would produce a
nonconstant finite-energy plane whose positive `dλ`-energy is captured in arbitrarily small
punctured discs about `0`). -/
theorem exists_norm_mul_gradNorm_le_near_puncture {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C := by
  sorry

end FiniteEnergyPlane
