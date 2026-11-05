-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_cylEndAt_of_gradNorm_tendsto
-- name    : FiniteEnergyPlane.isNondegenerateEnd_cylEndAt_of_gradNorm_tendsto
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:26:14.263447+00:00
-- url     : https://prove2.me/theorems/7815ec8a-c2a0-4dac-90f7-cfc0e002934c
-- title:
--   Gradient blow-up points of a convergent sequence of planes are negative punctures of the limit
-- statement:
--   Let $C>0$ be such that every periodic Reeb orbit of period at most $C$ on a strictly star-shaped level $S\subset\mathbb{R}^{2n+2}$ is nondegenerate. Let $u_k$ be finite-energy $\tilde J$-holomorphic planes with Hofer energy at most $C$, let $c_k>0$, and suppose that the radial rescalings $c_k u_k$ converge in $C^\infty_{\mathrm{loc}}(\mathbb{C}\setminus\Gamma)$, with $\Gamma$ finite, to a finite-energy $\tilde J$-holomorphic curve $w$ on $\mathbb{C}\setminus\Gamma$. If $z_0\in\Gamma$ is the limit of points $\zeta_k$ at which the gradients of $u_k$ tend to $\infty$, then $z_0$ is a negative puncture of $w$: $w$ is nondegenerately asymptotic at $z_0$ to a periodic orbit $Q$ of period at most $C$, the coordinate $a\circ w$ tends to $-\infty$ at $z_0$, and the action of $w$ on small counterclockwise circles about $z_0$ is bounded below by a positive constant.
--
--   This describes the punctures produced by gradient blow-up in compactness arguments for planes.
--
--   **Formalization Note** The end at $z_0$ is `IsNondegenerateEnd H w (cylEndAt z₀) Q (-1)`, with `cylEndAt z₀ s t = z₀ + e^{-2πs} e^{-2πit}`. The action on the circle of radius $\rho$ is `loopAction H w (fun t => z₀ + ccwLoop ρ t)`.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `C > 0` be such that every periodic Reeb orbit of period at most `C` is nondegenerate. Let `uₖ`
be finite-energy `J̃`-holomorphic planes with `E(uₖ) ≤ C`, let `cₖ > 0`, and suppose `cₖ • uₖ`
converge in `C^∞_loc(ℂ \ Γ)` to a finite-energy `J̃`-holomorphic curve `w` on `ℂ \ Γ`, `Γ` finite. If
`z₀ ∈ Γ` is a limit of points `ζₖ` with `gradNorm H uₖ (ζₖ) → ∞`, then `z₀` is a negative puncture of
`w`, nondegenerate over an orbit `Q` of period at most `C`: `aCoord H ∘ w → -∞` at `z₀`, and the
action of `w` along small counterclockwise circles about `z₀` is bounded below by a positive
constant. -/
theorem isNondegenerateEnd_cylEndAt_of_gradNorm_tendsto {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (C : ℝ) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate)
    (Γ : Finset ℂ) (w : ℂ → V n) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (u : ℕ → ℂ → V n) (hu : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k))
    (hE : ∀ k, energy H Set.univ (u k) ≤ ENNReal.ofReal C)
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (hconv : JHolomorphic.TendstoCInftyLocOn (fun k z => c k • u k z) w (↑Γ)ᶜ)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Γ) (ζ : ℕ → ℂ) (hζ : Tendsto ζ atTop (𝓝 z₀))
    (hblow : Tendsto (fun k => gradNorm H (u k) (ζ k)) atTop atTop) :
    ∃ Q : ReebOrbit H, Q.T ≤ C ∧ IsNondegenerateEnd H w (cylEndAt z₀) Q (-1) ∧
      Tendsto (fun z => aCoord H (w z)) (𝓝[≠] z₀) atBot ∧
      ∃ r η : ℝ, 0 < r ∧ 0 < η ∧ ∀ ρ ∈ Set.Ioo 0 r,
        η ≤ loopAction H w (fun t => z₀ + ccwLoop ρ t) := by
  sorry

end FiniteEnergyPlane
