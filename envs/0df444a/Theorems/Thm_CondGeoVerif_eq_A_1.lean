-- Prove2me | Theorems.Thm_CondGeoVerif_eq_A_1
-- name    : CondGeoVerif.eq_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:32:18.016858+00:00
-- url     : https://prove2.me/theorems/bc9b0f29-c1e7-442a-a1e2-82c4e1fc0a0e
-- title:
--   (A.1) — $\mathbb P\{\|\hat V_{C,R}-V_{C,R}\|_F>\xi\}\le2\cdot5^{dr}e^{-n\xi^2/(64B^2)}$
-- statement:
--   Fix an orthonormal basis $P\in\mathbb R^{d\times m}$, $k\le m\le d$, whose first $k$ columns are the candidate frame, a Borel rule $f$, and a Borel vector dual $\gamma:\mathbb R^m\to\mathbb R^r$ with $\|\gamma\|\le B$. Under any law of $(X,Y)$ with Gaussian feature marginal and arbitrary labels, let $\hat V_{C,R}$ be the empirical mean of $n$ i.i.d. observations $W=Z\gamma(U)^\top E_V\in\mathbb R^{d\times r}$ and $V_{C,R}=\mathbb EW$. For every $\xi>0$,
--   $$\mathbb P\{\|\hat V_{C,R}-V_{C,R}\|_F>\xi\}\le2\cdot5^{dr}\exp\{-n\xi^2/(64B^2)\}.\qquad(A.1)$$
--   The label need not be independent of the Gaussian coordinates. This is the honest prover's estimate of the residual matrices.
--
--   Differences from the source:
--   - generalization: B = 4 and r = min{k, d − m} → every B > 0 and every r; reason: the argument uses only ‖γ‖ ≤ B; the paper's values are a special case
--   - encoding: the empirical mean of n observations → (1/n)·∑ᵢ Wᵢ for every n ≥ 0; reason: at n = 0 the bound exceeds 1 and holds trivially
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §A.5, p.18 (PDF p.21), eq. (A.1)

import Mathlib
import Definitions.Def_CondGeoVerif_liftEnvelope
import Definitions.Def_CondGeoVerif_risk

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

namespace CondGeoVerif

/-- **The sub-Gaussian matrix estimate (A.1)** (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, §A.5, p.18 = PDF p.21). Fix a proposed
orthonormal basis `P ∈ ℝ^{d×m}` (first `k` columns the candidate frame), a Borel rule `f`, and a
Borel vector dual `γ : ℝᵐ → ℝʳ` with `‖γ‖ ≤ B`. For every law with Gaussian feature marginal and
arbitrary labels, the empirical mean `V̂_{C,R}` of `n` i.i.d. observations
`W = Zγ(U)ᵀE_V ∈ ℝ^{d×r}` satisfies
`P{‖V̂_{C,R} − V_{C,R}‖_F > ξ} ≤ 2 · 5^{dr} exp{−nξ²/(64B²)}`.

**Formalization Note** The paper fixes `B = 4` and `r = min{k, d − m}`; the statement is for every
`B > 0` and every `r`. The label need not be independent of the Gaussian coordinates. -/
theorem eq_A_1 {d m k r : ℕ} (hkm : k ≤ m) (hmd : m ≤ d) {B : ℝ} (hB : 0 < B)
    (f : Vec k → Bool) (hf : Measurable f) (P : Matrix (Fin d) (Fin m) ℝ) (hP : P ∈ stiefel d m)
    (γ : Vec m → Vec r) (hγ : Measurable γ) (hγB : ∀ u, ‖γ u‖ ≤ B)
    (μ : ProbabilityMeasure (Vec d × Bool)) (hμ : GaussMarginal (μ : Measure (Vec d × Bool)))
    (n : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    sampleLaw μ n
        {s | ξ < frob ((1 / (n : ℝ)) • (∑ i, matObs f P γ (s i)) -
          vecStat (μ : Measure (Vec d × Bool)) f P γ)}
      ≤ ENNReal.ofReal (2 * 5 ^ (d * r) * Real.exp (-((n : ℝ) * ξ ^ 2) / (64 * B ^ 2))) := by sorry

end CondGeoVerif
