-- Prove2me | Theorems.Thm_AgreementTop736_Exact_Supplement_theorem_9
-- name    : AgreementTop736.Exact.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:43:33.683109+00:00
-- url     : https://prove2.me/theorems/1ab32ff7-4d2d-4a58-a813-e1061c37aff6
-- title:
--   Theorem 9 — average Hamming, exact and approximate agreement bounds
-- statement:
--   Let $X$ and $\Sigma$ be finite. A valid sampling scheme has top size $q_k$, tested size $q_h$, and $0<q_h<q_k$. Let $a_x>0$ be the parent-independent inclusion probability for each element of positive marginal mass, and let $\xi=\min_x a_x$ on that support. Suppose every element-conditioned stationary top–test–top chain has spectral gap at least $\gamma>0$. For any local functions $F_K:K\to\Sigma$, let $\tau$ be the rejection probability of the exact equality test, with independent parents conditional on the sampled test face.
--
--   A coordinatewise majority exists. Every such majority $g$, including every tie choice, satisfies all four conclusions:
--   $$\mathbb E_K d(F_K,g|_K)\le\frac{q_h}{\gamma\xi}\tau,$$
--   $$\Pr_K[F_K\ne g|_K]\le\frac{q_h}{\gamma\xi}\tau,$$
--   $$\forall\delta>0,\qquad\Pr_K[d(F_K,g|_K)\ge\delta q_k]\le\frac{q_h}{\gamma\xi\delta q_k}\tau,$$
--   and, if $a_x=q_h/q_k$ for every supported element,
--   $$\mathbb E_K\frac{d(F_K,g|_K)}{q_k}\le\frac{\tau}{\gamma}.$$
--   Here $d$ counts differing coordinates, and the majority maximizes the label frequency under $\mu(\cdot\mid x\in K)$. The inclusion probabilities may vary with $x$ in the first three bounds; no variance assumption is made.
--
--   This companion theorem gives an average coordinate-error bound and its exact and approximate agreement consequences, while keeping the stronger normalized clause in the uniform-inclusion case.
--
--   Differences from the source:
--   - encoding: finite probability laws and local functions on their faces → finite weighted sums over subsets and total extensions F_K on X, with comparisons restricted to K or H; reason: every source assignment extends and all extra values have no effect; all conditional hypotheses omit zero-mass faces as in Section 2
--   - encoding: spectral gap of each stationary element-conditioned walk → the published Poincaré inequality with Dirichlet factor 1/2; reason: positive parent-independent inclusion gives the reversible stationary law μ_x by Section 2.2, making this the paper’s equivalent gap convention
--   - encoding: ξ=min_x a_x and the coordinatewise majority with arbitrary ties → the finite minimum on positive element support, existence of a majority, and bounds for every majority choice; reason: Section 2 omits zero-mass faces; valid sampling ensures nonempty support and a finite alphabet attains every maximum
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), p.12, Theorem 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Supplement_Hamming

namespace AgreementTop736.Exact.Supplement

/-- Theorem 9, p.12, all four conclusions. The Poincaré gap has the published 1/2
normalization. No uniform-inclusion or variance premise is assumed. -/
theorem theorem_9 {V : Type*} [Fintype V] [DecidableEq V]
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (a : V → ℝ)
    (ha : ParentIndependentInclusion S a) (γ : ℝ) (hγ : 0 < γ)
    (hgap : S.HasConditionedGap γ) (F : Finset V → V → α) :
    (∃ g : V → α, S.IsCoordMajority F g) ∧
    ∀ g : V → α, S.IsCoordMajority F g →
      averageError S F g ≤ (S.n : ℝ) / (γ * inclusionMinimum S a) * S.rejectionProb F ∧
      S.disagreementProb F g ≤ (S.n : ℝ) / (γ * inclusionMinimum S a) * S.rejectionProb F ∧
      (∀ δ : ℝ, 0 < δ → approximateDisagreementProb S F g δ ≤
        (S.n : ℝ) / (γ * inclusionMinimum S a * δ * (S.N : ℝ)) * S.rejectionProb F) ∧
      ((∀ x, 0 < S.pointMass x → a x = (S.n : ℝ) / (S.N : ℝ)) →
        normalizedAverageError S F g ≤ S.rejectionProb F / γ) := by sorry

end AgreementTop736.Exact.Supplement
