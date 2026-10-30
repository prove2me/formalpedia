-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_lemma_5_3
-- name    : CrossLayerControl.ECCA.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:42.155479+00:00
-- url     : https://prove2.me/theorems/74bbfcc5-fcd2-4818-835e-bb4f1046147b
-- title:
--   Lemma 5.3 (Lyapunov Drift)
-- statement:
--   Let $(\Omega,\Pr)$ be a probability space, let $\mathcal G_t$ be sub-$\sigma$-algebras (the information "$U(t)$"), let $\Lambda(t)\ge0$ be integrable random variables (the values $L(U(t))$ of a nonnegative Lyapunov function), and let $x(t)$, $y(t)$ be integrable random variables. If for every $t$, almost surely,
--   $$\mathbb E\{\Lambda(t+1)-\Lambda(t)\mid\mathcal G_t\}\le\mathbb E\{y(t)\mid\mathcal G_t\}-\mathbb E\{x(t)\mid\mathcal G_t\},\tag{5.17}$$
--   then
--   $$\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{x(\tau)\}\le\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{y(\tau)\},\qquad \liminf_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{x(\tau)\}\le\liminf_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{y(\tau)\}.$$
--
--   A drift inequality of the form (5.17) turns into a comparison of time averages. With $x$ the penalty and $y$ the bound of (6.11), it gives the throughput clause of Theorem 6.3.
--
--   Differences from the source:
--   - generalization: conditioning on U(t), with Λ(t) = L(U(t)) for a nonnegative function L → conditioning on an arbitrary sub-σ-algebra G_t, with an arbitrary nonnegative process Λ(t); reason: σ(U(t)) and L(U(t)) are a special case
--   - reading: E{L(U(0))} < ∞, and the drift (5.17) as a conditional expectation of L(U(t+1)) − L(U(t)) → Λ(t), x(t), y(t) integrable for every t; reason: the expectations in the statement and in its proof must exist; given E L(U(0)) < ∞, (5.17) makes every E L(U(t)) finite
--   - encoding: real limsup and liminf → limsup and liminf in EReal; reason: the averages may be unbounded; EReal avoids junk values
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Lemma 5.3, p. 81

import Mathlib

open MeasureTheory Filter

namespace CrossLayerControl.ECCA

/-- **Lemma 5.3 (Lyapunov Drift).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Lemma 5.3, p. 81: "Let E{L(U(0))} < ∞. If there exist scalar random
processes x(t) and y(t) such that for every timeslot t and for all possible values of U(t), the
Lyapunov drift satisfies: ∆(U(t)) ≤ E{y(t)|U(t)} − E{x(t)|U(t)}, (5.17) then:
limsup_{t→∞} (1/t) Σ_{τ=0}^{t−1} E{x(τ)} ≤ limsup_{t→∞} (1/t) Σ_{τ=0}^{t−1} E{y(τ)},
liminf_{t→∞} (1/t) Σ_{τ=0}^{t−1} E{x(τ)} ≤ liminf_{t→∞} (1/t) Σ_{τ=0}^{t−1} E{y(τ)}."
Context, p. 81: "Let L(U) be any non-negative function of U. … ∆(U(t)) ≜ E{L(U(t + 1)) −
L(U(t))|U(t)}".

Let `(Ω, Pr)` be a probability space, `m t` sub-σ-algebras (the information "U(t)"), `Lt t ≥ 0`
integrable random variables (the values `L(U(t))`), and `x t`, `y t` integrable random variables.
If for every `t`, almost surely
`E[Lt(t+1) − Lt(t) | m t] ≤ E[y(t) | m t] − E[x(t) | m t]`, then
`limsup (1/t) Σ_{τ<t} E x(τ) ≤ limsup (1/t) Σ_{τ<t} E y(τ)` and
`liminf (1/t) Σ_{τ<t} E x(τ) ≤ liminf (1/t) Σ_{τ<t} E y(τ)`.

**Formalization Note.** The paper conditions on `U(t)`; here `m t` is any sub-σ-algebra, which
contains the paper's case `m t = σ(U(t))`. The values `L(U(t))` are given directly as a nonnegative
process `Lt`. Integrability of `Lt t`, `x t`, `y t` is stated so that the expectations and
conditional expectations in (5.17) are defined (Lean's conditional expectation of a non-integrable
function is `0`). The `limsup`s and `liminf`s are taken in `EReal`, so they are never junk values. -/
theorem lemma_5_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ t, m t ≤ mΩ)
    (Lt x y : ℕ → Ω → ℝ) (hL : ∀ t ω, 0 ≤ Lt t ω) (hLi : ∀ t, Integrable (Lt t) Pr)
    (hx : ∀ t, Integrable (x t) Pr) (hy : ∀ t, Integrable (y t) Pr)
    (hdrift : ∀ t, condExp (m t) Pr (fun ω => Lt (t + 1) ω - Lt t ω) ≤ᵐ[Pr]
      fun ω => condExp (m t) Pr (y t) ω - condExp (m t) Pr (x t) ω) :
    limsup (fun t : ℕ => (((t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂Pr : ℝ) : EReal)) atTop ≤
      limsup (fun t : ℕ => (((t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂Pr : ℝ) : EReal))
        atTop ∧
    liminf (fun t : ℕ => (((t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂Pr : ℝ) : EReal)) atTop ≤
      liminf (fun t : ℕ => (((t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂Pr : ℝ) : EReal))
        atTop := by sorry

end CrossLayerControl.ECCA
