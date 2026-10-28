-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_bubble
-- name    : FiniteEnergyPlane.exists_bubble
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T23:25:36.960712+00:00
-- url     : https://prove2.me/theorems/5d13d907-23dc-4df4-b2af-1df9973dffea
-- title:
--   Gradient blow-up of finite-energy curves concentrates $d\lambda$-energy of at least a Reeb period
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $\Gamma\subset\mathbb{C}$ finite, and $U_k$ an increasing sequence of open sets with $\bigcup_kU_k=\mathbb{C}\setminus\Gamma$. Let $u_k$ be finite-energy $\tilde J$-holomorphic curves on $U_k$ with $E(u_k)\le C$, and $z_k\in U_k$ with $|\nabla u_k(z_k)|\to\infty$. Assume that the $z_k$ stay at distance $\ge\delta>0$ from $\Gamma$, and that either $(z_k)$ is bounded or some $U_m$ contains $\{|z|>R\}$ for some $R$. Then there are a subsequence $k_j$, points $z'_j$ with $|z_{k_j}-z'_j|\to0$, radii $r_j>0$ with $r_j\to0$ and $B_{r_j}(z'_j)\subseteq U_{k_j}$, and a periodic Reeb orbit $P=(x,T)$ with $T\le C$, such that
--   $$\limsup_{j\to\infty}\int_{B_{r_j}(z'_j)}u_{k_j}^*d\lambda_0\ \ge\ T.$$
--
--   **Formalization Note** $|\nabla u_k|$ is `gradNorm H (u k)`, the sum of the operator norms of $D(a\circ u_k)$ and $D(\mathrm{proj}\circ u_k)$, which is invariant under $y\mapsto cy$ like Hryniewicz's norm for an $\mathbb{R}$-invariant metric. Hryniewicz's $\sup_kE(u_k)=C<\infty$ is the bound $E(u_k)\le C$; his orbit is contractible, which is automatic since $S$ is a sphere. The hypothesis on the $z_k$ is stated explicitly here.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 2.20, p. 12

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Bubbling-off points: Hryniewicz 2014, Lemma 2.20. Let `Γ ⊆ ℂ` be finite, `U_k` an
increasing sequence of open sets exhausting `ℂ \ Γ`, and `u_k` finite-energy `J̃`-holomorphic
curves on `U_k` with energies at most `C`. Let `z_k ∈ U_k` with `|∇u_k(z_k)| → ∞` (in the
`ℝ`-invariant norm), where `z_k` stays away from `Γ` and either stays bounded or some `U_m`
contains a neighbourhood of `∞`. Then, along a subsequence, there are points `z'_j` with
`|z_{k_j} - z'_j| → 0`, radii `r_j → 0⁺` and a periodic Reeb orbit `P` of period `T ≤ C` such that
`limsup_j ∫_{B(z'_j, r_j)} u_{k_j}*dλ ≥ T`. -/
theorem exists_bubble {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUsub : ∀ k, U k ⊆ (↑Γ)ᶜ)
    (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (u : ℕ → ℂ → V n)
    (hu : ∀ k, IsFiniteEnergyCurve H J (U k) (u k)) (C : ℝ)
    (hC : ∀ k, energy H (U k) (u k) ≤ ENNReal.ofReal C) (z : ℕ → ℂ) (hz : ∀ k, z k ∈ U k)
    (hblow : Tendsto (fun k => gradNorm H (u k) (z k)) atTop atTop)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z' : ℕ → ℂ, ∃ r : ℕ → ℝ, ∃ P : ReebOrbit H,
      Tendsto (fun j => ‖z (φ j) - z' j‖) atTop (𝓝 0) ∧ (∀ j, 0 < r j) ∧
      Tendsto r atTop (𝓝 0) ∧ (∀ j, ball (z' j) (r j) ⊆ U (φ j)) ∧ P.T ≤ C ∧
      ENNReal.ofReal P.T ≤
        limsup (fun j => dlambdaEnergy H (ball (z' j) (r j)) (u (φ j))) atTop := by
  sorry

end FiniteEnergyPlane
