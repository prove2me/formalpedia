-- Prove2me | Theorems.Thm_CondGeoVerif_lemma_A_6
-- name    : CondGeoVerif.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:24:07.776462+00:00
-- url     : https://prove2.me/theorems/380125fb-a599-462d-9a9d-75be580daeca
-- title:
--   Lemma A.6 — uniform family modulus $\omega_F$
-- statement:
--   Let $F$ be a nonempty family of Borel rules $\mathbb R^K\to\{-1,1\}$, $K\ge1$, totally bounded in Gaussian disagreement $d_\gamma(f,g)=\mathbb P(f(G)\ne g(G))$. There is a nondecreasing $\omega_F$ tending to zero at zero such that, uniformly over ambient dimensions and orthonormal frames $W,W'\in\mathbb R^{d\times K}$,
--   $$\mathbb P(f(W^\top X)\ne g(W'^\top X))\le d_\gamma(f,g)+\omega_F(\|W-W'\|_F)\qquad\text{for all }f,g\in F,\ X\sim N(0,I_d).$$
--   This gives finite prediction nets for the whole union $\mathcal H_{F,d}$.
--
--   Differences from the source:
--   - encoding: ω_F nondecreasing, tending to zero at zero → ω : ℝ → ℝ, monotone on [0, ∞), with ω(s) → 0 as s ↓ 0; reason: only nonnegative arguments are used
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Lemma A.6, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_CondGeoVerif_GaussTotallyBounded

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel

namespace CondGeoVerif

/-- **Lemma A.6 (Uniform family modulus)** (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, p.21 = PDF p.24). Let `F` be a nonempty
family of Borel rules `ℝᴷ → {−1, 1}`, totally bounded in Gaussian disagreement
`d_γ(f, g) = P(f(G) ≠ g(G))`. There is a nondecreasing `ω_F` tending to zero at zero such that,
uniformly over ambient dimensions and orthonormal frames,
`P(f(WᵀX) ≠ g(W'ᵀX)) ≤ d_γ(f, g) + ω_F(‖W − W'‖_F)` for all `f, g ∈ F`, `X ∼ N(0, I_d)`.

**Formalization Note** `ω_F` is a function on `[0, ∞)` (monotone there), chosen before the rules,
the dimension and the frames. -/
theorem lemma_A_6 {K : ℕ} (hK : 1 ≤ K) (F : Set (Vec K → Bool)) (hFne : F.Nonempty)
    (hFm : ∀ f ∈ F, Measurable f) (hFtb : GaussTotallyBounded F) :
    ∃ ω : ℝ → ℝ, MonotoneOn ω (Set.Ici 0) ∧
      Filter.Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ f ∈ F, ∀ g ∈ F, ∀ d : ℕ, ∀ W ∈ stiefel d K, ∀ W' ∈ stiefel d K,
        (gauss d {x | frameRule f W x ≠ frameRule g W' x}).toReal ≤
          gaussDisagree f g + ω (frob (W - W')) := by sorry

end CondGeoVerif
