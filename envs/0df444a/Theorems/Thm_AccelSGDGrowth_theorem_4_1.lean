-- Prove2me | Theorems.Thm_AccelSGDGrowth_theorem_4_1
-- name    : AccelSGDGrowth.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:06.234662+00:00
-- url     : https://prove2.me/theorems/5f66d5e8-42d2-46e1-9726-0a64ce2be9e9
-- title:
--   Theorem 4.1 — the error recursion of DAM+ under the growth condition
-- statement:
--   Consider DAM+ (4.6) with $f\in\mathcal F(m,\mathcal L)$, $0<m\le\mathcal L$, minimizer $x_\star$, a positive weight sequence $(a_k)$, real step sizes $(\eta_k)$, and noise satisfying the growth condition with constants $\delta\ge0$, $\sigma^2\ge0$. Let $A_k=\sum_{i\le k}a_i$, $\rho_k=A_{k-1}/A_k$, and $V_k=U_k-L_k$ with $U_k=f(y_k)$ and $L_k$ of (4.3). Then for all $k\ge1$,
--   $$
--   \mathbb EV_{k+1}\le\rho_k\,\mathbb EV_k-\Big(\eta_k-\frac{(1+\delta)\mathcal L\eta_k^2}{2}-\frac{(1+\delta)a_k^2}{2A_k^2m}\Big)\mathbb E\|\nabla f_k\|^2+\Big(\frac{\mathcal L\eta_k^2}{2}+\frac{a_k^2}{2A_k^2m}\Big)\sigma^2 .
--   $$
--
--   This is the unified recursion (1.9) for DAM+: it holds for every $\delta\ge0$, which is why DAM+ keeps acceleration under any multiplicative noise level.
--
--   Differences from the source:
--   - generalization: noise ε_k drawn from ε(x_k), a family satisfying (1.7), with (2.5) derived from it → the conditional form (2.5) assumed directly: g_k is 𝒢_{k+1}-measurable, E[ε_k | 𝒢_k] = 0 and E[‖ε_k‖² | 𝒢_k] ≤ δ‖∇f(x_k)‖² + σ² a.s.; reason: every oracle of Definition 1.1 yields (2.5), so the paper's setting is a special case
--   - generalization: initial point x_1 left unspecified → x_1 random, 𝒢_1-strongly measurable with E‖x_1‖² < ∞; y_1 free; z_1 = 0 not assumed; reason: a deterministic x_1 is a special case; y_1 enters only through A_0/A_1 = 0, and (4.6a) at k = 1 forces z_1 = 0
--   - encoding: E‖ε_k‖² used without comment → ‖ε_k‖² integrable, as part of the growth condition; reason: Lean's conditional expectation of a non-integrable function is 0; the condition only excludes cases where the paper's expectations are undefined
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
--   - encoding: ρ_1 EV_1 at k = 1 → ρ_1 = A_0/A_1 = 0 multiplies the expectation of the junk V_1; reason: V_1 contains L_1, which divides by A_0 = 0; the paper's term is 0 as well
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Theorem 4.1, p.18

import Definitions.Def_AccelSGDGrowth_ClassF
import Definitions.Def_AccelSGDGrowth_GrowthCondition
import Definitions.Def_AccelSGDGrowth_IsDAMPlusRun
import Definitions.Def_AccelSGDGrowth_gapV

open MeasureTheory

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, Theorem 4.1, p.18. Consider DAM+ (4.6) under the growth
condition (Definition 1.1, in the form (2.5)) with constants `δ ≥ 0`, `σ² ≥ 0`, with `f ∈ F(m, L)`,
a positive weight sequence `a`, `A_k = Σ_{i≤k} a_i`, `ρ_k = A_{k−1}/A_k`, `V_k = U_k − L_k`,
`U_k = f(y_k)`, `L_k` of (4.3). Then for all `k ≥ 1`
`E V_{k+1} ≤ ρ_k E V_k − (η_k − (1+δ)Lη_k²/2 − (1+δ)a_k²/(2A_k²m)) E‖∇f_k‖² + (Lη_k²/2 + a_k²/(2A_k²m)) σ²`.

**Formalization Note.** The step sizes `η_k` are arbitrary reals, as on the page. `x_1` is
`𝒢_1`-measurable with `E‖x_1‖² < ∞` (random initial point allowed); `x⋆` is the minimizer. At `k = 1`,
`ρ_1 = 0` multiplies the junk `E V_1`. -/
theorem theorem_4_1 {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ mΩ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {m L δ sig2 : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hδ : 0 ≤ δ) (hsig : 0 ≤ sig2)
    (hf : ClassF m L f) (a η : ℕ → ℝ) (ha : ∀ k : ℕ, 1 ≤ k → 0 < a k)
    (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hrun : ∀ ω : Ω, IsDAMPlusRun m a η (fun k => x k ω) (fun k => y k ω) (fun k => z k ω)
      (fun k => g k ω))
    (hgrowth : GrowthCondition μ 𝒢 f x g δ sig2)
    (hx1 : StronglyMeasurable[𝒢 1] (x 1)) (hx1int : Integrable (fun ω => ‖x 1 ω‖ ^ 2) μ)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxstar : IsMinOn f Set.univ xstar)
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar (k + 1) ∂μ ≤
      cumWeight a (k - 1) / cumWeight a k *
          ∫ ω, gapV f m a (fun j => x j ω) (fun j => y j ω) (fun j => g j ω) xstar k ∂μ -
        (η k - (1 + δ) * L * η k ^ 2 / 2 - (1 + δ) * a k ^ 2 / (2 * cumWeight a k ^ 2 * m)) *
          ∫ ω, ‖gradient f (x k ω)‖ ^ 2 ∂μ +
        (L * η k ^ 2 / 2 + a k ^ 2 / (2 * cumWeight a k ^ 2 * m)) * sig2 := by sorry

end AccelSGDGrowth
