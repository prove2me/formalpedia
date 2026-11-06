-- Prove2me | Theorems.Thm_AnytimeAdaVR_proposition_D_1
-- name    : AnytimeAdaVR.proposition_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:38.672207+00:00
-- url     : https://prove2.me/theorems/0b24ddd3-96f0-4923-a231-b5859616f3cf
-- title:
--   Proposition D.1 — noiseless D-path bound (corrected: $\sqrt{2L\Delta_f}+L(N-1)$)
-- statement:
--   Suppose Assumptions 1 and 2 hold, and let the stochastic gradient be jointly measurable. For the D path from $x_{\mathrm{init}}$ with reservoir report $R_{D,N}$:
--
--   1. every D update has length at most one, $\|x_{t+1}-x_t\|\le1$;
--   2. for every $N\ge1$, $\|\nabla f(R_{D,N})\|\le\sqrt{2L\Delta_f}+L(N-1)$;
--   3. if the gradients are noiseless, then for every $N\ge1$,
--   $$
--   \mathbb E\,\|\nabla f(R_{D,N})\|\le\frac{D_0}{\sqrt N},\qquad D_0=2+2\Delta_f+2L\log\big(\max\{1,2L\}\big);
--   $$
--   4. $D_0\le 4(1+\Delta_f+L^2)$.
--
--   Item 2 gives the finite expected gradient norm that validation requires in every regime; item 3 is the noiseless rate supplied by the D path.
--
--   **Correction.** The paper prints item 2 as $\|\nabla f(R_{D,N})\|\le\sqrt{2L\Delta_f+L(N-1)}$ almost surely, which is false. Take $d=1$, $f(x)=50x^2$ ($L=100$), $x_{\mathrm{init}}=0$ ($\Delta_f=0$) and $g(x;\xi)=100x+\xi$ with $\xi=\pm1$ equally likely ($\sigma=1$). The first step gives $x_1=\mp1/\sqrt2$, so $\|\nabla f(x_1)\|=100/\sqrt2\approx70.7$, while $R_{D,2}=x_1$ with probability $1/2$ and the printed bound at $N=2$ is $10$. The paper's own argument ($\|\nabla f(x_{\mathrm{init}})\|\le\sqrt{2L\Delta_f}$, $\|x_t-x_{\mathrm{init}}\|\le t$, $L$-Lipschitz gradient) gives $\sqrt{2L\Delta_f}+Lt$, which is stated here. Theorem 2 is unaffected.
--
--   **Formalization Note** Items 1 and 2 are proved for every sample and coin sequence, not only almost surely.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: fresh independent samples, and reservoir coins independent of the samples → the path runs on an i.i.d. sample stream of law μ (Measure.infinitePi) and i.i.d. uniform coins on [0,1] (Measure.infinitePi of volume), combined by Measure.prod; reason: the probability model of pp.4 and 8 for one path; same law
--   - encoding: noiseless oracle: g(x; ξ) = ∇f(x) almost surely → Noiseless f g μ: for every x, g x ξ = ∇f(x) for μ-a.e. ξ; reason: fresh samples at every query make this the paper's almost-sure exactness at adaptive points; same instances
--   - correction: ‖∇f(R_{D,N})‖ ≤ √(2L∆f + L(N − 1)) almost surely → ‖∇f(R_{D,N})‖ ≤ √(2L∆f) + L(N − 1); reason: the printed bound is false: d = 1, f(x) = 50x² (L = 100), xinit = 0 (∆f = 0), g(x; ξ) = 100x + ξ with ξ = ±1 fair (σ = 1) gives ‖∇f(R_{D,2})‖ = 100/√2 ≈ 70.7 > 10 with probability 1/2; the proof's argument gives the corrected bound
--   - generalization: update length ≤ 1 and the gradient bound, almost surely → for every sample sequence and every coin sequence; reason: a pointwise statement implies the almost-sure one
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. D, Proposition D.1, p.24; eqs. (50)–(51), p.25

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_Noiseless
import Definitions.Def_AnytimeAdaVR_dReport
import Definitions.Def_AnytimeAdaVR_coefD0

namespace AnytimeAdaVR

open MeasureTheory

/-- **Proposition D.1 (Noiseless report bound), corrected: `√(2L∆f) + L(N − 1)`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. D,
pp.24–25: "Suppose Assumptions 1 and 2 hold. Every D update has length at most one, and, for each
deterministic N ≥ 1, ‖∇f(R_{D,N})‖ ≤ √(2L∆f + L(N − 1)) almost surely. … If the gradients are
noiseless, define D_0 = 2 + 2∆f + 2L log(max{1, 2L}), D_0 ≤ 4(1 + ∆f + L²). (50) Then, at every
deterministic integer local query count N ≥ 1, E‖∇f(R_{D,N})‖ ≤ D_0/√N. (51)"

Under Assumptions 1 and 2:
1. every D update has length at most one: `‖x_{t+1} − x_t‖ ≤ 1`;
2. for every `N ≥ 1`, `‖∇f(R_{D,N})‖ ≤ √(2L∆f) + L(N − 1)`;
3. for noiseless gradients, `E‖∇f(R_{D,N})‖ ≤ D_0/√N` for every `N ≥ 1`;
4. `D_0 ≤ 4(1 + ∆f + L²)`.

**Correction.** The printed clause 2 puts the root over both terms, `√(2L∆f + L(N − 1))`, which is
false: for `d = 1`, `f(x) = 50x²` (`L = 100`), `xinit = 0` (`∆f = 0`), `g(x; ξ) = 100x + ξ` with
`ξ = ±1` fair (`σ = 1`), the first step gives `x_1 = ∓1/√2` and `‖∇f(x_1)‖ = 100/√2 ≈ 70.7`, while
`R_{D,2} = x_1` with probability 1/2 and the printed bound at `N = 2` is `10`. The proof's own
argument (`‖∇f(xinit)‖ ≤ √(2L∆f)`, `‖x_t − xinit‖ ≤ t`, `L`-Lipschitz `∇f`) gives `√(2L∆f) + Lt`.

**Formalization Note.** Clauses 1–2 hold for every sample and coin sequence (the paper says
"almost surely"). The path runs on an i.i.d. sample stream and independent uniform coins; the
expectation is a lower integral. The stochastic gradient is jointly measurable. -/
theorem proposition_D_1 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)}
    {xinit : EuclideanSpace ℝ (Fin d)} {L Δf σ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hA1 : Assumption1 f L Δf xinit)
    (hA2 : Assumption2 f g μ σ) :
    (∀ (ξ : ℕ → Ξ) (t : ℕ), ‖(dSeq g xinit ξ (t + 1)).1 - (dSeq g xinit ξ t).1‖ ≤ 1) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ (ξ : ℕ → Ξ) (U : ℕ → unitInterval),
      ‖gradient f (dReport g xinit ξ U N)‖ ≤ Real.sqrt (2 * L * Δf) + L * ((N : ℝ) - 1)) ∧
    (Noiseless f g μ → ∀ N : ℕ, 1 ≤ N →
      ∫⁻ p, ‖gradient f (dReport g xinit p.1 p.2 N)‖ₑ
          ∂((Measure.infinitePi fun _ : ℕ => μ).prod
            (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))) ≤
        ENNReal.ofReal (coefD0 Δf L / Real.sqrt N)) ∧
    coefD0 Δf L ≤ 4 * (1 + Δf + L ^ 2) := by sorry

end AnytimeAdaVR
