-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_disk_round
-- name    : FiniteEnergyPlane.exists_subseq_tendsto_disk_round
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:11:12.312062+00:00
-- url     : https://prove2.me/theorems/0ea295f8-1288-418e-b638-e2e5bb709fe0
-- title:
--   Compactness of embedded holomorphic disks in the round sphere
-- statement:
--   Let $e$ embed $B_\rho$, $\rho>1$, into the round sphere $S^3\subset\mathbb{C}^2$, with characteristic field $V$. Let $K\subset B_\rho$ be compact such that $V$ has no zero on $K$ and $e(K)$ lies in an open half-space whose boundary contains the origin, and let $z_0\notin K$. Let $\Omega\subset B_\rho$ be open and $\Theta:\Omega\to S^1$ smooth with
--   $$d\Theta=i\,g\,\Theta\,e^*\lambda_0\quad\text{for a function }g>0,$$
--   and suppose every differentiable curve in $K$ is tangent to $V$ wherever it is not in $\Omega$. Let $\theta_1,\theta_2,\theta_3$ be distinct.
--
--   Let $u_\nu$ be embedded holomorphic disks with boundary loops $u_\nu(e^{2\pi it})=e(c_\nu(t))$, where $c_\nu$ is a loop in $K$ of winding number $1$ around $z_0$, such that $\Theta\circ c_\nu$ has degree $1$ and
--   $$\Theta(c_\nu(0))=\theta_1,\qquad\Theta(c_\nu(\tfrac14))=\theta_2,\qquad\Theta(c_\nu(\tfrac12))=\theta_3 .$$
--   Then a subsequence converges in $C^\infty$ on the closed unit disk to an embedded holomorphic disk with boundary loop in $e(K\cap\Omega)$, of winding number $1$ around $e(z_0)$.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$, and holomorphic refers to the standard structure $j_0$ on $\mathbb{R}\times S^3\cong\mathbb{C}^2\setminus\{0\}$. The function $\Theta$ is constant on the leaves in $\Omega$. No bound on energies or derivatives is assumed.
--
--   **Formalization Note** The complex structure is `roundJ`, and convergence is `TendstoCInftyLocWithin` on the closed disk. $\Theta$ is a map $\mathbb{C}\to\mathbb{C}$ with $|\Theta|=1$ on $\Omega$; no inclusion between $K$ and $\Omega$ is assumed, and the condition on curves holds trivially if $K\subset\Omega$. The degree is `HasLoopWind`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Proposition 34

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Proposition 34, for the round sphere with the standard complex structure. Let `e` embed the disk
of radius `ρ` into the round sphere, let `K` be a compact set in that disk on which the characteristic field has no zero and whose
image lies in an open half-space not containing the origin, and let `z₀ ∉ K`. Let `Ω` be open with a smooth map `Θ` to the unit circle whose
differential is a positive multiple of `e*λ₀`, and suppose that every differentiable curve in `K` is tangent to the
characteristic field wherever it is not in `Ω`. Consider embedded holomorphic disks with boundary
loops `c ν` in `K`, winding once around `z₀`, with `Θ ∘ c ν` of degree `1`, and with `Θ(c ν(0))`, `Θ(c ν(1/4))` and `Θ(c ν(1/2))` equal to
three fixed distinct values. A subsequence converges in `C^∞` on the closed disk to an embedded
holomorphic disk with boundary loop in `K ∩ Ω`, winding once around `z₀`. -/
theorem exists_subseq_tendsto_disk_round (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk roundH e ρ)
    (K : Set ℂ) (hK : IsCompact K) (hKρ : K ⊆ ball 0 ρ) (hK₀ : ∀ z ∈ K, charField e z ≠ 0)
    (p : V 1) (hp : ∀ z ∈ K, 0 < dot p (e z)) (z₀ : ℂ) (hz₀ : z₀ ∉ K)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hΩρ : Ω ⊆ ball 0 ρ) (Θ : ℂ → ℂ) (g : ℂ → ℝ) (hΘ : ContDiffOn ℝ ∞ Θ Ω)
    (hΘ' : ∀ z ∈ Ω, ‖Θ z‖ = 1 ∧ 0 < g z ∧ ∀ w : ℂ, fderiv ℝ Θ z w =
      ((g z * liouville (e z) (fderiv ℝ e z w) : ℝ) : ℂ) * Complex.I * Θ z)
    (htan : ∀ c : ℝ → ℂ, (∀ t, c t ∈ K) → Differentiable ℝ c → ∀ t, c t ∉ Ω →
      ∃ a : ℝ, deriv c t = a • charField e (c t))
    (θ₁ θ₂ θ₃ : ℂ) (h₁₂ : θ₁ ≠ θ₂) (h₂₃ : θ₂ ≠ θ₃) (h₁₃ : θ₁ ≠ θ₃)
    (u : ℕ → ℂ → V 1) (c : ℕ → ℝ → ℂ) (hu : ∀ ν, IsEmbeddedHoloDisk roundH roundJ e z₀ K (u ν))
    (hc : ∀ ν, HasDiskBoundary e z₀ K (u ν) (c ν)) (hcΘ : ∀ ν, HasLoopWind (fun t => Θ (c ν t)) 1)
    (hc' : ∀ ν, Θ (c ν 0) = θ₁ ∧ Θ (c ν (1 / 4)) = θ₂ ∧ Θ (c ν (1 / 2)) = θ₃) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → V 1,
      TendstoCInftyLocWithin (fun ν => u (φ ν)) v (closedBall 0 1) ∅ ∧
      IsEmbeddedHoloDisk roundH roundJ e z₀ (K ∩ Ω) v := by
  sorry

end FiniteEnergyPlane
