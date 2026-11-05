-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_atTop_of_unbounded_on_compact
-- name    : FiniteEnergyPlane.exists_subseq_tendsto_atTop_of_unbounded_on_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T18:14:25.927541+00:00
-- url     : https://prove2.me/theorems/2d8fac1d-ed4e-4ccd-9291-0f410e057b84
-- title:
--   A family of continuous functions unbounded on a compact set blows up at a point
-- statement:
--   Let $g_k : \mathbb{C} \to \mathbb{R}$ be continuous and let $K \subset \mathbb{C}$ be compact. Suppose that for every $M \in \mathbb{R}$ there are $k$ and $z \in K$ with $g_k(z) > M$. Then there are a strictly increasing sequence $\theta(k)$, points $\zeta_k \in \mathbb{C}$ and a point $z \in K$ with $\zeta_k \to z$ and $g_{\theta(k)}(\zeta_k) \to +\infty$.
--
--   This locates a blow-up point for gradient norms of sequences of curves that are not locally uniformly bounded.
--
--   Formalization Note: the indices $\theta(k)$ are required to be strictly increasing, not just unbounded; a single $g_k$ is bounded above on $K$.
-- source:
--   Standard; used as in U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Corollary 4.10

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `g k : ℂ → ℝ` be continuous and unbounded above on the compact set `Kc`, as a family: for every
`M` some `g k` exceeds `M` at a point of `Kc`. Then along a subsequence there are points `ζ k` converging
to a point of `Kc` with `g (θ k) (ζ k) → ∞`. -/
theorem exists_subseq_tendsto_atTop_of_unbounded_on_compact (g : ℕ → ℂ → ℝ)
    (hg : ∀ k, Continuous (g k)) (Kc : Set ℂ) (hKc : IsCompact Kc)
    (hun : ∀ M : ℝ, ∃ k, ∃ z ∈ Kc, M < g k z) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ ζ : ℕ → ℂ, ∃ z ∈ Kc, Tendsto ζ atTop (𝓝 z) ∧
      Tendsto (fun k => g (θ k) (ζ k)) atTop atTop := by
  sorry

end FiniteEnergyPlane
