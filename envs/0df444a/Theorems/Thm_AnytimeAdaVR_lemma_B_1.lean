-- Prove2me | Theorems.Thm_AnytimeAdaVR_lemma_B_1
-- name    : AnytimeAdaVR.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:21.41823+00:00
-- url     : https://prove2.me/theorems/a17b82e3-cbc3-4fcc-8708-4246b893d57a
-- title:
--   Lemma B.1 — block mean error and second-half maximum $\le 2E^2/b$
-- statement:
--   Assume Assumptions 1 and 2, and for an M block also average smoothness (Assumption 3) with constant $\bar L$. Put $\Lambda=L$ for S and $\Lambda=\bar L$ for M, and $E=4\sqrt{\sigma^2+\Lambda^2}$. Consider one block of Algorithm 2 with scale $a\ge1$ and even length $b\ge2$, run on fresh samples, with errors $e_t=v_t-\nabla f(x_t)$, $1\le t\le b$. Conditionally on the history at the block's start,
--   $$
--   \mathbb E_j\Big(\frac1b\sum_{t=1}^b\|e_t\|\Big)^2\le\frac{2E^2}{b},\qquad \mathbb E_j\max_{b/2<t\le b}\|e_t\|^2\le\frac{2E^2}{b}.
--   $$
--   The conditioning precedes the block's success or failure. These bounds control the descent of each block and the gradient at the stored candidate of a failed block.
--
--   **Formalization Note** The block's samples are independent of the history, so the conditional expectation is the expectation over the block's samples with the start $(x,a,b)$ frozen; the statement is made for every such start.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: E_j: expectation conditional on the history at the start of block j → expectation over the block's fresh i.i.d. samples, for a deterministic start (x, a, b); reason: the block's samples are independent of the history, so the conditional expectation equals this integral evaluated at the random start
--   - generalization: every block of Algorithm 2 → every start point x, every scale a ≥ 1 and every even length b ≥ 2; reason: every block of Algorithm 2 has a ≥ 1 and even b ≥ 2, so the statement specializes to each block
--   - encoding: the block's samples ξ_1, …, ξ_b → an i.i.d. stream ℕ → Ξ of law μ (Measure.infinitePi), of which the first b are read; reason: same law of the samples the block uses
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. B, Lemma B.1, eq. (33), p.17; setting p.16

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_AvgSmooth
import Definitions.Def_AnytimeAdaVR_blockSeq
import Definitions.Def_AnytimeAdaVR_coefE

namespace AnytimeAdaVR

open MeasureTheory

/-- **Lemma B.1 (Mean error and second-half maximum).** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. B, p.17, eq. (33): "For every
block of Algorithm 2, under the assumptions stated above,
E_j((1/b) Σ_{t=1}^b ‖e_t‖)² ≤ 2E²/b, E_j max_{b/2<t≤b} ‖e_t‖² ≤ 2E²/b. The conditioning precedes the
block's success or failure." The assumptions (App. B, p.16) are Assumptions 1 and 2, plus
Assumption 3 for M; `e_t = v_t − ∇f(x_t)`, `E = 4√(σ² + Λ²)` with `Λ = L` for S and `Λ = L̄` for M;
"Within one block, a, b, η are fixed at their starting values. … All block lengths are even."

For a block of kind `k` started at any point `x` with any scale `a ≥ 1` and any even length
`b ≥ 2`, run on i.i.d. samples of law `μ`, both bounds hold.

**Formalization Note.** `E_j` is the expectation given the history at the block's start. The
block's samples are fresh, so it equals the expectation over the block's samples with the start
`(x, a, b)` frozen; this is stated for every deterministic start. Every block of Algorithm 2 has
`a ≥ 1` and even `b ≥ 2`. Samples are a stream `ℕ → Ξ` under `Measure.infinitePi` (only the first
`b` are read). Expectations are lower integrals. Steps are numbered `t = 1, …, b`;
`(blockSeq … t).2.1 = x_t` and `(blockSeq … t).2.2 = v_t`. -/
theorem lemma_B_1 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)}
    {xinit : EuclideanSpace ℝ (Fin d)} {L Δf σ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hA1 : Assumption1 f L Δf xinit)
    (hA2 : Assumption2 f g μ σ)
    (k : SMKind) (Λ : ℝ) (hΛ : (k = .S ∧ Λ = L) ∨ (k = .M ∧ AvgSmooth g μ Λ))
    (x : EuclideanSpace ℝ (Fin d)) (a : ℝ) (ha : 1 ≤ a) (b : ℕ) (hb : 2 ≤ b) (hbe : Even b) :
    let e : (ℕ → Ξ) → ℕ → EuclideanSpace ℝ (Fin d) := fun ξ t =>
      (blockSeq k g x a b ξ t).2.2 - gradient f (blockSeq k g x a b ξ t).2.1
    (∫⁻ ξ, ENNReal.ofReal (((b : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 b, ‖e ξ t‖) ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => μ) ≤ ENNReal.ofReal (2 * coefE σ Λ ^ 2 / b)) ∧
    (∫⁻ ξ, (⨆ t ∈ Finset.Ioc (b / 2) b, ‖e ξ t‖ₑ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => μ) ≤ ENNReal.ofReal (2 * coefE σ Λ ^ 2 / b)) := by sorry

end AnytimeAdaVR
