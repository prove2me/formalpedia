-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_rescaled_punctured
-- name    : FiniteEnergyPlane.exists_subseq_tendsto_rescaled_punctured
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T21:58:21.70083+00:00
-- url     : https://prove2.me/theorems/55a5054f-2859-413d-b939-1ce2a16f1292
-- title:
--   Normalized rescalings at a puncture converge to a curve with zero dλ-energy
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Assume the gradient bound near the puncture: there are $r>0$ and $C$ with $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$, where $|\nabla u|=\|Da\|+\|Dw\|$. Let $\rho_k\to0$ with $\rho_k>0$. Then there are a subsequence $\rho_{k_j}$ and a finite-energy $\tilde J$-holomorphic curve $v:\mathbb C\setminus\{0\}\to\mathbb R^{2n+2}\setminus\{0\}$ with $\int_{\mathbb C\setminus\{0\}}v^*d\lambda=0$ such that the normalized rescalings
--   $$v_j(z)=e^{-2a(u(\rho_{k_j}))}\,u(\rho_{k_j}z)$$
--   converge to $v$ in $C^\infty_{\mathrm{loc}}(\mathbb C\setminus\{0\})$.
--
--   This is the puncture counterpart of `exists_subseq_tendsto_rescaled_plane` (rescalings of a plane at infinity); it is the blow-up step in the asymptotic analysis of a finite-energy curve at a nonremovable puncture.
--
--   **Formalization Note** In the coordinates $y=e^{2a}x$ ($x\in S$) of $\mathbb R^{2n+2}\setminus\{0\}$, multiplying by $e^{-2a(u(\rho_k))}$ is the $\mathbb R$-translation by $-a(u(\rho_k))$. $u$ is a function on all of $\mathbb C$; only its values on `ball 0 1 \ {0}` matter. The rescaled maps are defined on all of $\mathbb C$ and are $\tilde J$-holomorphic on $\{0<|z|<1/\rho_k\}$. $C^\infty_{\mathrm{loc}}$ convergence is `JHolomorphic.TendstoCInftyLocOn` on `{z | z ≠ 0}`; the gradient bound is the hypothesis `hG` with `gradNorm`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, proof of Theorem 9.8; H. Hofer, Invent. Math. 114 (1993), Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of the normalized rescalings at a puncture. Let `u` be a finite-energy
`J̃`-holomorphic curve on the punctured unit disc with the gradient bound
`|z| |∇u(z)| ≤ C` for `0 < |z| < r`, and let `ρ_k → 0⁺`. Then along a subsequence the maps
`z ↦ e^{-2a(u(ρ_k))} u(ρ_k z)` converge in `C^∞_loc(ℂ \ {0})` to a finite-energy
`J̃`-holomorphic curve `w` on `ℂ \ {0}` with zero `dλ`-energy. -/
theorem exists_subseq_tendsto_rescaled_punctured {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      dlambdaEnergy H {z | z ≠ 0} w = 0 ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j z => Real.exp (-2 * aCoord H (u ((ρ (φ j) : ℝ) : ℂ))) • u (((ρ (φ j) : ℝ) : ℂ) * z))
        w {z | z ≠ 0} := by
  sorry

end FiniteEnergyPlane
