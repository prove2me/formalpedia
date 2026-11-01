-- Prove2me | Theorems.Thm_DRSubmodHull_lemma_3_3_concave_nonneg_direction
-- name    : DRSubmodHull.lemma_3_3_concave_nonneg_direction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:14.693508+00:00
-- url     : https://prove2.me/theorems/60077376-824f-4182-8305-8ec9f8dd54de
-- title:
--   Lemma 3.3 (corrected: f concave along each coordinate) — DR-submodular functions are concave along non-negative directions
-- statement:
--   Let $\mathcal X=[a,b]\subseteq\mathbb R^V$ be a box and let $f$ be DR-submodular on $\mathcal X$ and concave along each coordinate on $\mathcal X$. Let $z\in\mathcal X$, let $d\ge 0$ be a non-negative direction with $z+d\in\mathcal X$, and let $0\le t\le 1$. Then
--   $$
--   f(z+td)-f(z)\;\ge\;t\,\big[f(z+d)-f(z)\big].
--   $$
--
--   The function $s\mapsto f(z+sd)$ is thus concave-like along non-negative directions; this is the inequality used in Lemma 6.3 and in Lemmas 6.8, 6.9 to compare $f$ along the segments that build the DR inequalities.
--
--   The paper states the lemma with the condition that the coordinate paths $z+\sum_{j\le i}d_je^j$ and $z+t\sum_{j\le i}d_je^j$ stay in $\mathcal X$; on a box this holds exactly when $z\in\mathcal X$ and $z+d\in\mathcal X$.
--
--   Differences from the source:
--   - correction: f DR-submodular on 𝒳 → f DR-submodular and concave along each coordinate on the box 𝒳 = [a, b]; reason: the printed lemma is false: one coordinate, 𝒳 = [0, 2], f = A with A : ℝ → ℝ ℚ-linear, A(1) = 0, A(√2) = 1 is DR-submodular, and z = 0, d = √2, t = 1/√2 give A(1) = 0 < (1/√2)·A(√2); the proof's Lemma 3.2 (p.33) passes from midpoint concavity to concavity without regularity
--   - reading: 𝒳 = ∏ᵢ 𝒳ᵢ with 𝒳ᵢ compact (closed intervals for continuous i; §3, p.5) → 𝒳 = Set.Icc a b, a real box on every coordinate; reason: the paper applies the lemma at fractional points of integer coordinates (Lemma 6.3's proof, Lemmas 6.8, 6.9), so the integer coordinates' domains are real intervals
--   - encoding: z + ∑_{j≤i} d_j eʲ, z + t∑_{j≤i} d_j eʲ ∈ 𝒳 for all i → z ∈ 𝒳 and z + d ∈ 𝒳; reason: on a box, with d ≥ 0 and 0 ≤ t ≤ 1, all path points lie between z and z + d, so the two conditions are equivalent
--   - encoding: coordinates 1, …, n + m → an arbitrary finite type V of coordinates; reason: relabelling of coordinates; same instances
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Lemma 3.3, p.6 (§3 setting p.5; proof p.33)

import Mathlib
import Definitions.Def_DRSubmodHull_IsDRSubmodularOn

set_option autoImplicit false

namespace DRSubmodHull

/-- **Lemma 3.3 (corrected)** (Yu, Küçükyavuz, arXiv:2211.07726v2, §3, p.6). Let `f` be
DR-submodular and concave along each coordinate on a box `𝒳 = [a, b] ⊆ ℝ^V`. For `z ∈ 𝒳`, a
non-negative direction `d ≥ 0` and `0 ≤ t ≤ 1` such that the coordinate paths
`z + ∑_{j ≤ i} d_j eʲ` and `z + t ∑_{j ≤ i} d_j eʲ` stay in `𝒳`,
`f(z + t d) − f(z) ≥ t [f(z + d) − f(z)]`.

**Formalization Note.** §3 takes `f` on a product `∏ᵢ 𝒳ᵢ` of intervals; here `𝒳 = Set.Icc a b`
(real intervals on every coordinate). On a box the path condition holds iff `z ∈ 𝒳` and
`z + d ∈ 𝒳`, which is how it is stated. The hypothesis `IsCoordConcaveOn` is the correction: the
printed lemma is false without it (one coordinate, `f` a ℚ-linear `A` with `A(1) = 0`,
`A(√2) = 1`, `z = 0`, `d = √2`, `t = 1/√2`). -/
theorem lemma_3_3_concave_nonneg_direction {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V → ℝ) (f : (V → ℝ) → ℝ)
    (hDR : IsDRSubmodularOn (Set.Icc a b) f) (hconc : IsCoordConcaveOn (Set.Icc a b) f)
    (z d : V → ℝ) (hz : z ∈ Set.Icc a b) (hd : 0 ≤ d) (hzd : z + d ∈ Set.Icc a b)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (f (z + d) - f z) ≤ f (z + t • d) - f z := by sorry

end DRSubmodHull
