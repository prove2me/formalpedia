-- Prove2me | Theorems.Thm_CondGeoVerif_bessel_count
-- name    : CondGeoVerif.bessel_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:14:48.667964+00:00
-- url     : https://prove2.me/theorems/f291f53d-d754-47ab-b9ad-fca9973bf291
-- title:
--   §A.6.1 — Bessel count of revealed directions (corrected: strict inequality only for at least one addition)
-- statement:
--   Let $F_1,\dots,F_N$ be pairwise orthogonal in $L^2$ of a probability space, with $\mathbb EF_j^2\le B^2$ ($B>0$), and let $e$ be measurable with $0\le e\le1$ and $|\mathbb E[eF_j]|>t/(16\sqrt k)$ for every $j$ ($t>0$, $k\ge1$). Then
--   $$N\,\frac{t^2}{256kB^2}\le\sum_j\frac{|\mathbb E[eF_j]|^2}{\mathbb EF_j^2}\le\mathbb Ee^2\le1,$$
--   and the first inequality is strict when $N\ge1$.
--
--   In the paper $F_j(X)=\gamma_{j,\ell}(U_j)(n_j\cdot X)$ are the witnesses of the directions appended by the honest prover and $e=e_V$; the count bounds the number of revealed directions independently of $d$.
--
--   Differences from the source:
--   - generalization: the constructed witnesses F_j = γ_{j,ℓ}(U_j)(n_j · X) and e = e_V → any pairwise orthogonal L² family with E F_j² ≤ B² and any measurable e with 0 ≤ e ≤ 1 and the witness bounds; reason: the paper establishes exactly these properties of its construction before applying Bessel's inequality
--   - correction: #{additions}·t²/(256kB²) < ∑_j |E[e F_j]|²/E F_j² → ≤ always, and < when N ≥ 1; reason: with no additions (N = 0) both sides are 0, so the strict inequality is false; it satisfies every assumption
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §A.6.1, p.19 (PDF p.22)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **The Bessel count of revealed directions** (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, §A.6.1, p.19 = PDF p.22). Let
`F₁, …, F_N` be pairwise orthogonal in `L²` with `EF_j² ≤ B²`, and let `e` be a measurable function
with `0 ≤ e ≤ 1` and `|E[eF_j]| > t/(16√k)` for every `j` (the witnesses of the `N` added
directions). Then
`N · t²/(256kB²) ≤ ∑_j |E[eF_j]|²/EF_j² ≤ Ee² ≤ 1`, with strict first inequality when `N ≥ 1`.

**Formalization Note** Stated for an abstract family in `L²` of a probability space; in the paper
`F_j(X) = γ_{j,ℓ}(U_j)(n_j · X)` and `e = e_V`. At `N = 0` both sides of the first inequality are
`0`, so the paper's strict inequality is asserted only for `N ≥ 1`. -/
theorem bessel_count {Ω : Type} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω) {k N : ℕ}
    (hk : 1 ≤ k) {B t : ℝ} (hB : 0 < B) (ht : 0 < t) (F : Fin N → Ω → ℝ)
    (hF : ∀ j, MemLp (F j) 2 (μ : Measure Ω))
    (horth : ∀ i j, i ≠ j → ∫ ω, F i ω * F j ω ∂(μ : Measure Ω) = 0)
    (hFB : ∀ j, ∫ ω, F j ω ^ 2 ∂(μ : Measure Ω) ≤ B ^ 2)
    (e : Ω → ℝ) (he : Measurable e) (he01 : ∀ ω, 0 ≤ e ω ∧ e ω ≤ 1)
    (hwit : ∀ j, t / (16 * Real.sqrt k) < |∫ ω, e ω * F j ω ∂(μ : Measure Ω)|) :
    (N : ℝ) * (t ^ 2 / (256 * k * B ^ 2)) ≤
        ∑ j, |∫ ω, e ω * F j ω ∂(μ : Measure Ω)| ^ 2 / ∫ ω, F j ω ^ 2 ∂(μ : Measure Ω) ∧
    (0 < N → (N : ℝ) * (t ^ 2 / (256 * k * B ^ 2)) <
        ∑ j, |∫ ω, e ω * F j ω ∂(μ : Measure Ω)| ^ 2 / ∫ ω, F j ω ^ 2 ∂(μ : Measure Ω)) ∧
    ∑ j, |∫ ω, e ω * F j ω ∂(μ : Measure Ω)| ^ 2 / ∫ ω, F j ω ^ 2 ∂(μ : Measure Ω) ≤
        ∫ ω, e ω ^ 2 ∂(μ : Measure Ω) ∧
    ∫ ω, e ω ^ 2 ∂(μ : Measure Ω) ≤ 1 := by sorry

end CondGeoVerif
