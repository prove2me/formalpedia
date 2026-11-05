-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn
-- name    : FiniteEnergyPlane.isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:19:47.152666+00:00
-- url     : https://prove2.me/theorems/9f24fd9c-4a74-43f9-b00a-0adc25f25502
-- title:
--   Limits of normalized fast planes keep the asymptotic orbit at $\infty$
-- statement:
--   Let $P=(x,T)$ be a periodic Reeb orbit on a strictly star-shaped level $S\subset\mathbb{R}^4$ such that every periodic orbit of period at most $T$ is nondegenerate, and let $0<\gamma$ be smaller than every such period and every difference of two distinct such periods. Let $u_k$ be a sequence in the set $\Theta(K,P)$ of fast finite-energy planes asymptotic to $P$ at $\infty$ with $u_k(0)\in K$ and $d\lambda$-energy $\gamma$ outside the closed unit disk. Suppose a sequence of radial rescalings of the $u_k$ converges in $C^\infty_{\mathrm{loc}}(\mathbb{C}\setminus\Gamma)$, with $\Gamma$ a finite subset of the closed unit disk, to a finite-energy $\tilde J$-holomorphic curve $w$ on $\mathbb{C}\setminus\Gamma$. Then $w$ has a nondegenerate positive puncture at $\infty$ over $P$, and the action of $w$ on circles of radius $\rho$ tends to $T$ as $\rho\to\infty$.
--
--   This identifies the behaviour at $\infty$ of every limit of such a sequence.
--
--   **Formalization Note** $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$ is `V 1 \ {0}`, with $a$ = `aCoord H` and $\mathrm{pr}$ = `proj H`; $\Theta$ = `fastPlaneSet H J P K γ`. The rescaling is `(Real.exp (-(2 * a_k 2))) • u_k`; the end is `IsNondegenerateEnd H w cylInf P 1`, and the action is `loopAction H w (ccwLoop ρ)`.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` and `γ` be as in `exists_loop_near_orbit_of_mem_fastPlaneSet`, let `uₖ` be a sequence in
`fastPlaneSet H J P K γ`, and suppose the shifted planes `e^{-2aₖ(2)} • uₖ` converge in
`C^∞_loc(ℂ \ Γ)` to a finite-energy `J̃`-holomorphic curve `w` on `ℂ \ Γ`, with `Γ` a finite subset
of the closed unit disk. Then `w` has a nondegenerate positive puncture at `∞` over the same orbit
`P`, and the actions `∫_{|z| = ρ} w*λ` tend to `P.T` as `ρ → ∞`. -/
theorem isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (Γ : Finset ℂ) (hΓ : ∀ z ∈ Γ, ‖z‖ ≤ 1) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (hconv : JHolomorphic.TendstoCInftyLocOn
      (fun k z => Real.exp (-(2 * aCoord H (u k 2))) • u k z) w (↑Γ)ᶜ) :
    IsNondegenerateEnd H w cylInf P 1 ∧
      Tendsto (fun ρ : ℝ => loopAction H w (ccwLoop ρ)) atTop (𝓝 P.T) := by
  sorry

end FiniteEnergyPlane
