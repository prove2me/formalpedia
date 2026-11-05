-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_bounded_off_finite_of_concentration
-- name    : FiniteEnergyPlane.exists_subseq_bounded_off_finite_of_concentration
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:54:24.381072+00:00
-- url     : https://prove2.me/theorems/940bf11b-a501-4003-b0f9-31674ae1f520
-- title:
--   Finite blow-up sets of continuous functions from mass concentration
-- statement:
--   Let $g_k : \mathbb{C} \to \mathbb{R}$ be continuous functions, and $f_k : \mathbb{C} \to [0,\infty]$ functions with $\int_{\mathbb{C}} f_k \le T$ for all $k$, where $T \ge 0$; let $\gamma > 0$. Assume that for every subsequence $g_{\psi(k)}$ and every sequence $\zeta_k \to z$ with $g_{\psi(k)}(\zeta_k) \to +\infty$, there is a further subsequence along which, for each $\delta > 0$, eventually $\int_{B_\delta(z)} f > \gamma$.
--
--   Then there are a subsequence $\varphi$ and a finite set $\Gamma \subset \mathbb{C}$ with $\#\Gamma \cdot \gamma \le T$ such that:
--
--   (1) $g_{\varphi(k)}$ is uniformly bounded above on every compact subset of $\mathbb{C} \setminus \Gamma$;
--
--   (2) every $z \in \Gamma$ is a limit of points $\zeta_k$ with $g_{\varphi(k)}(\zeta_k) \to +\infty$, and for each $\delta > 0$, eventually $\int_{B_\delta(z)} f_{\varphi(j)} > \gamma$.
--
--   This is the abstract selection step of bubbling-off analysis, applicable to gradient norms of pseudoholomorphic curves with bounded area.
--
--   Formalization Note: $g_k$ and $f_k$ need no further structure. In particular $f_k$ is not assumed measurable, the integrals being lower Lebesgue integrals (`lintegral`).
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Corollaries 4.9 and 4.10

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Finite blow-up sets from mass concentration. Let `g k : ℂ → ℝ` be continuous and `f k : ℂ → ℝ≥0∞`
have total integral at most `T`, with `0 < γ`. Suppose that along every subsequence, every blow-up
of `g` at a point `z` (a sequence `ζ_k → z` with `g (ψ k) (ζ k) → ∞`) has a further subsequence on
which each ball about `z` eventually carries `f`-mass greater than `γ`. Then there are a subsequence
and a finite set `Γ` with `#Γ · γ ≤ T` such that `g` is uniformly bounded on every compact subset of
`ℂ \ Γ`, and every point of `Γ` is a blow-up point of `g` with this mass concentration. -/
theorem exists_subseq_bounded_off_finite_of_concentration (g : ℕ → ℂ → ℝ)
    (hg : ∀ k, Continuous (g k)) (f : ℕ → ℂ → ℝ≥0∞) (T γ : ℝ) (hγ : 0 < γ) (hT0 : 0 ≤ T)
    (hT : ∀ k, ∫⁻ z, f k z ≤ ENNReal.ofReal T)
    (hQ : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (ζ : ℕ → ℂ) (z : ℂ), Tendsto ζ atTop (𝓝 z) →
      Tendsto (fun k => g (ψ k) (ζ k)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ δ > 0, ∀ᶠ j in atTop,
        ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (ψ (φ j)) w) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (Γ.card : ℝ) * γ ≤ T ∧
      (∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, g (φ k) z ≤ M) ∧
      ∀ z ∈ Γ, (∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧
          Tendsto (fun k => g (φ k) (ζ k)) atTop atTop) ∧
        ∀ δ > 0, ∀ᶠ j in atTop, ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (φ j) w := by
  sorry

end FiniteEnergyPlane
