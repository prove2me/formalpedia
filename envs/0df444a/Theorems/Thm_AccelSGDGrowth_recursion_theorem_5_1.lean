-- Prove2me | Theorems.Thm_AccelSGDGrowth_recursion_theorem_5_1
-- name    : AccelSGDGrowth.recursion_theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:13.766498+00:00
-- url     : https://prove2.me/theorems/5efabc84-77d8-40db-a6a7-799097cb10ab
-- title:
--   The recursion in the proof of Theorem 5.1 (corrected: for $k\ge2$)
-- statement:
--   In the setting of Theorem 4.1, assume in addition $a_k/A_k=\sqrt{m\mathcal L}\,\eta_k$ (so $a_k^2/A_k^2=m\mathcal L\eta_k^2$) for every $k\ge2$. Then for every $k\ge2$:
--
--   1. $\mathbb EV_{k+1}\le(1-\sqrt{m\mathcal L}\,\eta_k)\,\mathbb EV_k-\big(\eta_k-(1+\delta)\mathcal L\eta_k^2\big)\mathbb E\|\nabla f_k\|^2+\mathcal L\eta_k^2\sigma^2$;
--   2. if $\eta_k\le1/(2(1+\delta)\mathcal L)=1/\gamma_4$, then
--   $$
--   \mathbb EV_{k+1}\le(1-\sqrt{m\mathcal L}\,\eta_k)\,\mathbb EV_k-\frac{\eta_k}{2}\mathbb E\|\nabla f_k\|^2+\mathcal L\eta_k^2\sigma^2 ;
--   $$
--   3. $\mathbb EV_k\ge0$.
--
--   This casts DAM+ as the abstract recursion (5.2) with $(e_k,s_k)=(\mathbb EV_k,\mathbb E\|\nabla f(x_k)\|^2)$ and $(\gamma_1,\gamma_2,\gamma_3,\gamma_4)=(\sqrt{m\mathcal L},1/2,\mathcal L\sigma^2,2\mathcal L(1+\delta))$.
--
--   Differences from the source:
--   - correction: a_k/A_k = √(mL) η_k (for all k ≥ 1) → imposed for k ≥ 2 only; reason: A_1 = a_1 gives a_1/A_1 = 1, while √(mL)η_1 = 1/(2(1+δ)√κ) ≤ 1/2 in the first phase; e.g. m = L = 1, δ = 0, α = 1 admits no positive weight sequence satisfying the printed condition; a_1 > 0 stays free and only ratios enter the scheme
--   - generalization: the two displayed inequalities → also the conclusion EV_k ≥ 0 for k ≥ 2; reason: an extra conjunct, implied by f(y_k) − f(x⋆) ≤ V_k (p.16, Step 1) and Lemma 4.1(c); the page's two inequalities are the other conjuncts
--   - generalization: noise ε_k drawn from ε(x_k), a family satisfying (1.7), with (2.5) derived from it → the conditional form (2.5) assumed directly: g_k is 𝒢_{k+1}-measurable, E[ε_k | 𝒢_k] = 0 and E[‖ε_k‖² | 𝒢_k] ≤ δ‖∇f(x_k)‖² + σ² a.s.; reason: every oracle of Definition 1.1 yields (2.5), so the paper's setting is a special case
--   - generalization: initial point x_1 left unspecified → x_1 random, 𝒢_1-strongly measurable with E‖x_1‖² < ∞; y_1 free; z_1 = 0 not assumed; reason: a deterministic x_1 is a special case; y_1 enters only through A_0/A_1 = 0, and (4.6a) at k = 1 forces z_1 = 0
--   - encoding: E‖ε_k‖² used without comment → ‖ε_k‖² integrable, as part of the growth condition; reason: Lean's conditional expectation of a non-integrable function is 0; the condition only excludes cases where the paper's expectations are undefined
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, proof of Theorem 5.1, p.24 (and p.22)

import Definitions.Def_AccelSGDGrowth_ClassF
import Definitions.Def_AccelSGDGrowth_GrowthCondition
import Definitions.Def_AccelSGDGrowth_IsDAMPlusRun
import Definitions.Def_AccelSGDGrowth_gapV

open MeasureTheory

namespace AccelSGDGrowth

/-- The recursion in the proof of Chen, Na, Kolar, arXiv:2006.06782v4, Theorem 5.1, p.24.
In the setting of Theorem 4.1, assume `a_k/A_k = √(mL) η_k` (so `a_k²/A_k² = mLη_k²`) for every
`k ≥ 2`. Then for every `k ≥ 2`:
1. `E V_{k+1} ≤ (1 − √(mL)η_k) E V_k − (η_k − (1+δ)Lη_k²) E‖∇f_k‖² + Lη_k²σ²`;
2. if `η_k ≤ 1/(2(1+δ)L) = 1/γ₄`, then `E V_{k+1} ≤ (1 − √(mL)η_k) E V_k − (η_k/2) E‖∇f_k‖² + Lη_k²σ²`;
3. `E V_k ≥ 0`.

**Formalization Note.** The relation `a_k/A_k = √(mL)η_k` is imposed for `k ≥ 2` only, and the
conclusions are for `k ≥ 2`: at `k = 1`, `a_1/A_1 = 1` for every positive weight sequence, so the
printed relation cannot hold there when `√(mL)η_1 < 1` (correction). -/
theorem recursion_theorem_5_1 {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ mΩ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {m L δ sig2 : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hδ : 0 ≤ δ) (hsig : 0 ≤ sig2)
    (hf : ClassF m L f) (a η : ℕ → ℝ) (ha : ∀ k : ℕ, 1 ≤ k → 0 < a k)
    (hratio : ∀ k : ℕ, 2 ≤ k → a k / cumWeight a k = Real.sqrt (m * L) * η k)
    (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hrun : ∀ ω : Ω, IsDAMPlusRun m a η (fun k => x k ω) (fun k => y k ω) (fun k => z k ω)
      (fun k => g k ω))
    (hgrowth : GrowthCondition μ 𝒢 f x g δ sig2)
    (hx1 : StronglyMeasurable[𝒢 1] (x 1)) (hx1int : Integrable (fun ω => ‖x 1 ω‖ ^ 2) μ)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxstar : IsMinOn f Set.univ xstar)
    (k : ℕ) (hk : 2 ≤ k) :
    ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar (k + 1) ∂μ ≤
      (1 - Real.sqrt (m * L) * η k) *
          ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar k ∂μ -
        (η k - (1 + δ) * L * η k ^ 2) * ∫ ω, ‖gradient f (x k ω)‖ ^ 2 ∂μ +
        L * η k ^ 2 * sig2 ∧
    (η k ≤ 1 / (2 * (1 + δ) * L) →
      ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar (k + 1) ∂μ ≤
        (1 - Real.sqrt (m * L) * η k) *
            ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar k ∂μ -
          η k / 2 * ∫ ω, ‖gradient f (x k ω)‖ ^ 2 ∂μ +
          L * η k ^ 2 * sig2) ∧
    0 ≤ ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar k ∂μ := by sorry

end AccelSGDGrowth
