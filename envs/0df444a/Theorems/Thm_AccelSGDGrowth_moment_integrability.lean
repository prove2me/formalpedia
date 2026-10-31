-- Prove2me | Theorems.Thm_AccelSGDGrowth_moment_integrability
-- name    : AccelSGDGrowth.moment_integrability
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:41.943589+00:00
-- url     : https://prove2.me/theorems/5ad87d2e-6de0-4e28-87d2-c3a0cca60b82
-- title:
--   Moment bounds (a) — measurability and integrability along DAM+
-- statement:
--   On a probability space with filtration $(\mathcal G_k)$, let $0<m\le\mathcal L$, $f\in\mathcal F(m,\mathcal L)$, $\delta,\sigma^2\ge0$, positive weights $(a_k)$, arbitrary real step sizes $(\eta_k)$, sequences $x,y,z,g$ forming a run of DAM+ (4.6) at every outcome, the growth condition (2.5), and an initial point $x_1$ that is $\mathcal G_1$-measurable with $\mathbb E\|x_1\|^2<\infty$. Then for every $k\ge1$ and every point $x_\star$:
--
--   1. $x_k$ is $\mathcal G_k$-measurable;
--   2. $\|x_k\|^2$, $\|g_k\|^2$, $\|y_{k+1}\|^2$, $\|z_{k+1}\|^2$, $f(x_k)$, $f(y_{k+1})$, $L_{k+1}$ and $\|\nabla f(x_k)\|^2$ are integrable.
--
--   The paper takes these expectations without comment ("Multiplying (4.16) by $1/A_k$ and taking full expectation on both sides", p.19); this item makes every expectation in Theorems 4.1 and 5.1 a genuine one.
--
--   Differences from the source:
--   - reading: expectations of V_k, ‖∇f_k‖², ‖g_k‖² taken without stating integrability (p.19) → an explicit measurability and integrability statement; reason: no statement exists on the page; this is the property the proof presupposes
--   - generalization: noise ε_k drawn from ε(x_k), a family satisfying (1.7), with (2.5) derived from it → the conditional form (2.5) assumed directly: g_k is 𝒢_{k+1}-measurable, E[ε_k | 𝒢_k] = 0 and E[‖ε_k‖² | 𝒢_k] ≤ δ‖∇f(x_k)‖² + σ² a.s.; reason: every oracle of Definition 1.1 yields (2.5), so the paper's setting is a special case
--   - generalization: initial point x_1 left unspecified → x_1 random, 𝒢_1-strongly measurable with E‖x_1‖² < ∞; y_1 free; z_1 = 0 not assumed; reason: a deterministic x_1 is a special case; y_1 enters only through A_0/A_1 = 0, and (4.6a) at k = 1 forces z_1 = 0
--   - encoding: E‖ε_k‖² used without comment → ‖ε_k‖² integrable, as part of the growth condition; reason: Lean's conditional expectation of a non-integrable function is 0; the condition only excludes cases where the paper's expectations are undefined
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, implicit in the proof of Theorem 4.1, pp.18–19 (no label)

import Definitions.Def_AccelSGDGrowth_ClassF
import Definitions.Def_AccelSGDGrowth_GrowthCondition
import Definitions.Def_AccelSGDGrowth_IsDAMPlusRun
import Definitions.Def_AccelSGDGrowth_lowerL

open MeasureTheory

namespace AccelSGDGrowth

/-- Moment bounds, part (a): measurability and integrability along a DAM+ run. No label in the
paper; implicit in the proof of Chen, Na, Kolar, arXiv:2006.06782v4, Theorem 4.1, pp.18–19
("Multiplying (4.16) by 1/A_k and taking full expectation on both sides, we obtain", p.19).

On a probability space with filtration `𝒢`, let `f ∈ F(m, L)` (`0 < m ≤ L`), `δ, σ² ≥ 0`, positive
weights `a`, arbitrary real step sizes `η`, sequences `x, y, z, g` forming a DAM+ run (4.6) at every
outcome, the growth condition (2.5), and `x_1` that is `𝒢_1`-strongly measurable with `E‖x_1‖² < ∞`.
Then for every `k ≥ 1` and every point `x⋆`: `x_k` is `𝒢_k`-strongly measurable, and `‖x_k‖²`,
`‖g_k‖²`, `‖y_{k+1}‖²`, `‖z_{k+1}‖²`, `f(x_k)`, `f(y_{k+1})`, `L_{k+1}` and `‖∇f(x_k)‖²` are integrable.

**Formalization Note.** This is what makes every expectation in Theorem 4.1 and Theorem 5.1 a genuine
integral (a Bochner integral of a non-integrable function is `0`). -/
theorem moment_integrability {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ mΩ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {m L δ sig2 : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hδ : 0 ≤ δ) (hsig : 0 ≤ sig2)
    (hf : ClassF m L f) (a η : ℕ → ℝ) (ha : ∀ k : ℕ, 1 ≤ k → 0 < a k)
    (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hrun : ∀ ω : Ω, IsDAMPlusRun m a η (fun k => x k ω) (fun k => y k ω) (fun k => z k ω)
      (fun k => g k ω))
    (hgrowth : GrowthCondition μ 𝒢 f x g δ sig2)
    (hx1 : StronglyMeasurable[𝒢 1] (x 1)) (hx1int : Integrable (fun ω => ‖x 1 ω‖ ^ 2) μ)
    (xstar : EuclideanSpace ℝ (Fin d)) (k : ℕ) (hk : 1 ≤ k) :
    StronglyMeasurable[𝒢 k] (x k) ∧
    Integrable (fun ω => ‖x k ω‖ ^ 2) μ ∧
    Integrable (fun ω => ‖g k ω‖ ^ 2) μ ∧
    Integrable (fun ω => ‖y (k + 1) ω‖ ^ 2) μ ∧
    Integrable (fun ω => ‖z (k + 1) ω‖ ^ 2) μ ∧
    Integrable (fun ω => f (x k ω)) μ ∧
    Integrable (fun ω => f (y (k + 1) ω)) μ ∧
    Integrable (fun ω => lowerL f m a (fun j => x j ω) (fun j => g j ω) xstar (k + 1)) μ ∧
    Integrable (fun ω => ‖gradient f (x k ω)‖ ^ 2) μ := by sorry

end AccelSGDGrowth
