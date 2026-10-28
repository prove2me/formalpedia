-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_bubbling_plane
-- name    : FiniteEnergyPlane.exists_bubbling_plane
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-25T23:47:32.210554+00:00
-- url     : https://prove2.me/theorems/13375ffb-d036-45a4-86d1-d86b4114b9b4
-- title:
--   Bubbling-off analysis: the rescaled limit plane at a blow-up point
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with a $d\lambda_0$-compatible complex structure $J$ on $\xi$, and let $\tilde J$ be the induced $\mathbb R$-invariant almost complex structure on the symplectization $\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$. Let $\Gamma\subset\mathbb C$ be finite, $U_1\subset U_2\subset\cdots$ open sets with $\bigcup_k U_k=\mathbb C\setminus\Gamma$, and $u_k:U_k\to\mathbb R\times S$ finite-energy $\tilde J$-holomorphic curves with Hofer energy $E(u_k)\le C$. Let $z_k\in U_k$ with $|\nabla u_k(z_k)|\to\infty$ (in the $\mathbb R$-invariant norm $|\nabla a|+|\nabla(\mathrm{proj}\circ u)|$), $\operatorname{dist}(z_k,\Gamma)\ge\delta>0$, and assume either that $(z_k)$ is bounded or that some $U_m$ contains $\{|w|>R\}$.
--
--   Then there are a subsequence $u_{k_j}$, points $z'_j$ with $|z_{k_j}-z'_j|\to 0$, scales $R_j\to\infty$ and a nonconstant finite-energy $\tilde J$-holomorphic plane $v:\mathbb C\to\mathbb R\times S$ with $E(v)\le C$, such that for every $\rho>0$: the discs $B(z'_j,\rho/R_j)$ lie in $U_{k_j}$ for all large $j$, and
--   $$\int_{B(0,\rho)}v^*d\lambda\;\le\;\liminf_{j\to\infty}\int_{B(z'_j,\rho/R_j)}u_{k_j}^*d\lambda .$$
--
--   Proof idea (Hofer; Hryniewicz, proof of Lemma 2.20): the hypotheses on $z_k$ give $\kappa>0$ with $\overline B(z_k,\kappa)\subset U_k$ for large $k$. Hofer's lemma applied to $|\nabla u_k|$ on $\overline B(z_k,\kappa)$ with $\varepsilon_{0,k}=|\nabla u_k(z_k)|^{-1/2}$ yields $z'_k$, $\varepsilon_k\le\varepsilon_{0,k}$ with $|z'_k-z_k|\le 2\varepsilon_{0,k}$, $\varepsilon_kR_k\to\infty$ for $R_k=|\nabla u_k(z'_k)|$, and $|\nabla u_k|\le 2R_k$ on $\overline B(z'_k,\varepsilon_k)$. The rescalings $v_k(w)=e^{-2a(u_k(z'_k))}u_k(z'_k+w/R_k)$ on $B(0,\varepsilon_kR_k)$ have $|\nabla v_k|\le 2$, $|\nabla v_k(0)|=1$, $a(v_k(0))=0$ and energy $\le C$, and their $d\lambda$-energy on $B(0,\rho)$ equals that of $u_k$ on $B(z'_k,\rho/R_k)$ (platform lemma `rescale_isFiniteEnergyCurve`). Elliptic compactness (platform lemma `exists_plane_of_gradNorm_le`) gives a $C^\infty_{loc}$ limit plane $v$ with the stated properties.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), proof of Lemma 2.20; H. Hofer, Invent. Math. 114 (1993), pp. 535-537 (bubbling-off analysis)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Bubbling-off analysis: the rescaled limit plane (Hofer 1993, pp. 535–537; Hryniewicz 2014,
proof of Lemma 2.20). In the situation of Lemma 2.20 (finite-energy `J̃`-holomorphic curves
`u_k` on an exhaustion `U_k` of `ℂ \ Γ` with energies `≤ C`, and points `z_k ∈ U_k` with
`|∇u_k(z_k)| → ∞` staying away from `Γ`, and either bounded or eventually in a fixed
neighbourhood `{|w| > R} ⊆ U_m` of `∞`), there are a subsequence `u_{k_j}`, points `z'_j` with
`|z_{k_j} - z'_j| → 0` and scales `R_j → ∞`, and a nonconstant finite-energy `J̃`-holomorphic plane
`v` with Hofer energy `≤ C`, such that for every `ρ > 0` the discs `B(z'_j, ρ / R_j)` eventually
lie in `U_{k_j}` and `∫_{B(0, ρ)} v*dλ ≤ liminf_j ∫_{B(z'_j, ρ / R_j)} u_{k_j}*dλ`. (The plane is
the limit of the rescalings `w ↦ e^{-2 a(u_{k_j}(z'_j))} u_{k_j}(z'_j + w / R_j)`, where `z'_j` is
obtained from Hofer's lemma and `R_j = |∇u_{k_j}(z'_j)|`.) -/
theorem exists_bubbling_plane {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUsub : ∀ k, U k ⊆ (↑Γ)ᶜ)
    (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (u : ℕ → ℂ → V n)
    (hu : ∀ k, IsFiniteEnergyCurve H J (U k) (u k)) (C : ℝ)
    (hC : ∀ k, energy H (U k) (u k) ≤ ENNReal.ofReal C) (z : ℕ → ℂ) (hz : ∀ k, z k ∈ U k)
    (hblow : Tendsto (fun k => gradNorm H (u k) (z k)) atTop atTop)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m)  :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z' : ℕ → ℂ, ∃ R : ℕ → ℝ, ∃ v : ℂ → V n,
      Tendsto (fun j => ‖z (φ j) - z' j‖) atTop (𝓝 0) ∧ (∀ j, 0 < R j) ∧
      Tendsto R atTop atTop ∧ IsFiniteEnergyCurve H J Set.univ v ∧ (∃ z₁ z₂, v z₁ ≠ v z₂) ∧
      energy H Set.univ v ≤ ENNReal.ofReal C ∧
      ∀ ρ : ℝ, 0 < ρ → (∀ᶠ j in atTop, ball (z' j) (ρ / R j) ⊆ U (φ j)) ∧
        dlambdaEnergy H (ball 0 ρ) v ≤
          liminf (fun j => dlambdaEnergy H (ball (z' j) (ρ / R j)) (u (φ j))) atTop := by
  sorry


end FiniteEnergyPlane
