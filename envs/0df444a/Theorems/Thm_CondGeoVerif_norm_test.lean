-- Prove2me | Theorems.Thm_CondGeoVerif_norm_test
-- name    : CondGeoVerif.norm_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:20:13.08553+00:00
-- url     : https://prove2.me/theorems/943f9a90-7ba8-4e8b-96b8-36ba6e1d0ff4
-- title:
--   §A.5 — U-statistic norm test, $\mathbb EU_n=\|\mu\|^2$, $\mathrm{Var}(U_n)$, error $\le1/16$
-- statement:
--   Let $W_1,\dots,W_n$ be i.i.d. vectors in $\mathbb R^p$, $p\ge1$, with mean $\mu$ and covariance $\Sigma\preceq B^2I$ ($B>0$), $n\ge2$, and
--   $$U_n=\frac1{n(n-1)}\sum_{i\ne j}\langle W_i,W_j\rangle .$$
--   Then
--   $$\mathbb EU_n=\|\mu\|^2,\qquad\mathrm{Var}(U_n)=\frac{4\mu^\top\Sigma\mu}n+\frac{2\operatorname{tr}(\Sigma^2)}{n(n-1)}.$$
--   For $t>0$ and $n\ge\max\{2,512B^2\sqrt p/t^2\}$, the test that accepts when $U_n\le t^2/2$ errs with probability at most $1/16$ in either case: $\mathbb P(U_n>t^2/2)\le1/16$ if $\|\mu\|\le t/4$, and $\mathbb P(U_n\le t^2/2)\le1/16$ if $\|\mu\|>t$.
--
--   This is the $\sqrt d$-sample test of a residual mean norm.
--
--   Differences from the source:
--   - generalization: B = 4 ("Throughout this section let B = 4") → every B > 0; reason: the computation does not use the value of B; B = 4 is a special case
--   - encoding: W with mean µ and covariance Σ ⪯ B²I → a law with finite second moment, µ its mean, Σ its covariance matrix, and E⟨v, W − µ⟩² ≤ B²‖v‖² for every v; reason: equivalent formulation
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §A.5, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_CondGeoVerif_projClass

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **The U-statistic norm test** (Chen, *The Conditional Geometry of Statistical Verification*,
manuscript, October 2026, sha256 07a66d18…, §A.5, p.18 = PDF p.21). Let `W₁, …, W_n` be i.i.d.
vectors in `ℝᵖ` with mean `µ` and covariance `Σ ⪯ B²I`, and
`U_n = (1/(n(n − 1))) ∑_{i≠j} ⟨W_i, W_j⟩`. Then `EU_n = ‖µ‖²` and
`Var(U_n) = 4µᵀΣµ/n + 2 tr(Σ²)/(n(n − 1))`. For `n ≥ max{2, 512B²√p/t²}`, comparison with
`t²/2` accepts (`U_n ≤ t²/2`) if `‖µ‖ ≤ t/4` and rejects if `‖µ‖ > t`, with error at most `1/16`
in either case.

**Formalization Note** The law `ν` of `W` has a finite second moment; `Σ ⪯ B²I` is
`E⟨v, W − µ⟩² ≤ B²‖v‖²` for every `v`. The paper fixes `B = 4` in §A.5; the statement is for every
`B > 0`. The variance is `E(U_n − EU_n)²`. -/
theorem norm_test {p : ℕ} (hp : 1 ≤ p) {B t : ℝ} (hB : 0 < B) (ht : 0 < t)
    (ν : ProbabilityMeasure (Vec p)) (h2 : MemLp id 2 (ν : Measure (Vec p)))
    (hcov : ∀ v : Vec p,
      ∫ w, (inner ℝ v (w - ∫ w', w' ∂(ν : Measure (Vec p)))) ^ 2 ∂(ν : Measure (Vec p)) ≤
        B ^ 2 * ‖v‖ ^ 2)
    (n : ℕ) (hn : 2 ≤ n) :
    let μ : Vec p := ∫ w, w ∂(ν : Measure (Vec p))
    let Cov : Matrix (Fin p) (Fin p) ℝ := fun a b => ∫ w, (w a - μ a) * (w b - μ b) ∂(ν : Measure (Vec p))
    let U : (Fin n → Vec p) → ℝ := fun W =>
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) * ∑ i, ∑ j, if i = j then 0 else inner ℝ (W i) (W j)
    let πn : Measure (Fin n → Vec p) := Measure.pi (fun _ : Fin n => (ν : Measure (Vec p)))
    (∫ W, U W ∂πn = ‖μ‖ ^ 2) ∧
    (∫ W, (U W - ‖μ‖ ^ 2) ^ 2 ∂πn =
      4 * (∑ a, ∑ b, μ a * Cov a b * μ b) / n + 2 * (Cov * Cov).trace / ((n : ℝ) * ((n : ℝ) - 1))) ∧
    (512 * B ^ 2 * Real.sqrt p / t ^ 2 ≤ n →
      (‖μ‖ ≤ t / 4 → πn {W | t ^ 2 / 2 < U W} ≤ ENNReal.ofReal (1 / 16)) ∧
      (t < ‖μ‖ → πn {W | U W ≤ t ^ 2 / 2} ≤ ENNReal.ofReal (1 / 16))) := by sorry

end CondGeoVerif
