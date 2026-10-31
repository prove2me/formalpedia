-- Prove2me | Theorems.Thm_DynTargetMV_lemma_3
-- name    : DynTargetMV.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:38.444997+00:00
-- url     : https://prove2.me/theorems/553ca862-4994-4598-9ab6-eca3f915f1f2
-- title:
--   Lemma 3 — freezing a Lipschitz spike at $a(t,x)$ is $o(\varepsilon)$ in mean, variance and covariance
-- statement:
--   Let $r,b,\sigma$ be bounded deterministic functions and $W$ a standard $d$-dimensional Brownian motion. Fix $t\ge0$, $x\in\mathbb R$ and $T>t$. Let $a(s,y)$ be a deterministic function with $\lim_{s\downarrow t}(a(s,x)-a(t,x))=0$, and assume there exist $\bar\varepsilon\in(0,T-t)$ and $L>0$ such that
--   $$
--   \|a(s,y)-a(s,y')\|\le L|y-y'|\quad\text{for all } s\in[t,t+\bar\varepsilon],\ y,y'\in\mathbb R.
--   $$
--   Let $\hat\pi(s,y):=u(s)y+v(s)$ with $u,v$ deterministic and square-integrable on $[t,T]$. Let $X_1^\varepsilon$ and $X_2^\varepsilon$ be the wealth processes from $X(t)=x$ of the strategies that follow, respectively, $a(s,y)$ and the constant $a(t,x)$ on $[t,t+\varepsilon)$, and $\hat\pi$ afterwards, and put $Y^\varepsilon:=X_1^\varepsilon-X_2^\varepsilon$. Then, for $i=1,2$ and all $p\ge1$,
--   $$
--   \lim_{\varepsilon\downarrow0}E_t\Bigl[\frac{Y^\varepsilon(T)}\varepsilon\Bigr]=0,\quad
--   \lim_{\varepsilon\downarrow0}E_t\Bigl[\frac{Y^\varepsilon(T)X_i^\varepsilon(T)}\varepsilon\Bigr]=0,\quad
--   \lim_{\varepsilon\downarrow0}E_t\Bigl[\Bigl(\frac{|Y^\varepsilon(T)|}{\sqrt\varepsilon}\Bigr)^p\Bigr]=0,
--   $$
--   and consequently
--   $$
--   \lim_{\varepsilon\downarrow0}\frac{\operatorname{var}_t(Y^\varepsilon(T))}\varepsilon=\lim_{\varepsilon\downarrow0}\frac{\operatorname{cov}_t(Y^\varepsilon(T),X_i^\varepsilon(T))}\varepsilon=0 .
--   $$
--   This transfers the closed-form computations for strategies affine in wealth to the constant-dollar spikes of Definition 1.
--
--   Differences from the source:
--   - encoding: a standard d-dimensional Brownian motion, with the filtration left implicit → IsStdBM: a filtered probability space with the usual conditions, Brownian on [0,T], coordinates given by the published BrownianOn, coordinate increments independent, vector increment independent of F r; reason: strong solutions live on the augmented Brownian filtration, which satisfies the usual conditions, and only [0,T] is used
--   - encoding: the Itô integral ∫π⊤σ dW → the sum over j of published HasItoIntegral integrals against W j, with the integrand set to 0 at the single time T, plus a.s. finite energy of π; reason: a strategy is a function on [0,T), the time T is null, and the energy clause follows from Assumption 1 (ii) for any Itô integrand
--   - encoding: E_t, var_t, cov_t → expectation, variance and covariance of the solutions started at (t,x); reason: the start is deterministic
--   - reading: for each ε ∈ (0,ε̄), the two processes → solutions are required only for ε small, as eventually-in-ε families of unique strong solutions; reason: a(·,x) is controlled only near t, so the source's estimates apply for small ε
--   - encoding: deterministic functions r, b, σ, a, u, v → these functions are measurable (a jointly; the others on [0,T] or [t,T)); reason: needed for the wealth equation to make sense; the source leaves it implicit
--   - encoding: the expectations are taken as finite → the conclusion also states that the terminal wealths are in Lᵖ for every p ≥ 1, eventually in ε; reason: so that no expectation is a junk value; this follows from (B.9)
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Lemma 3, p.23

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_spike
import Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom
import Definitions.Def_DynTargetMV_IsStdBM

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology

namespace DynTargetMV

/-- **Lemma 3.** Replacing a Lipschitz spike `a(s,y)` on `[t,t+ε)` by its frozen value `a(t,x)` changes the
terminal wealth by `o(ε)` in mean and variance, in covariance with the wealth, and by `o(√ε)` in every
`Lᵖ`, when `π̂(s,y) = u(s)y + v(s)` is followed after `t+ε`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Lemma 3, p.23.

**Formalization Note** Lemma 3 has its own bounded `r, b, σ`, not Assumption 1; they, `a`, `u`, `v` are
measurable, which the source leaves implicit. The solutions `X₁ ε`, `X₂ ε` are required only for small
`ε`, since `a(·,x)` is controlled only near `t`; `Tendsto … (𝓝[>] 0)` is `lim_{ε↓0}`. The clause
`MemLp` records that all moments are finite, so that no expectation below is a junk value; it follows
from (B.9). `‖·‖` in the Lipschitz condition is Euclidean. -/
theorem lemma_3 {m d n : ℕ} (M : Market m d n)
    (hr : Measurable (fun s : Icc 0 M.T => M.r s))
    (hb : Measurable (fun s : Icc 0 M.T => M.b s))
    (hσ : ∀ i j, Measurable (fun s : Icc 0 M.T => M.σ s i j))
    (hrb : ∃ K : ℝ, ∀ s, 0 ≤ s → |M.r s| ≤ K)
    (hbb : ∃ K : ℝ, ∀ s, 0 ≤ s → ∀ i, |M.b s i| ≤ K)
    (hσb : ∃ K : ℝ, ∀ s, 0 ≤ s → ∀ i j, |M.σ s i j| ≤ K)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T)
    {t x : ℝ} (ht : 0 ≤ t) (htT : t < M.T)
    (a : ℝ → ℝ → Fin m → ℝ) (ha : Measurable (fun p : ℝ × ℝ => a p.1 p.2))
    (halim : Tendsto (fun s => a s x - a t x) (𝓝[>] t) (𝓝 0))
    {εbar L : ℝ} (hεbar : εbar ∈ Ioo 0 (M.T - t)) (hL : 0 < L)
    (hLip : ∀ s ∈ Icc t (t + εbar), ∀ y y' : ℝ,
      Real.sqrt (sqNorm (a s y - a s y')) ≤ L * |y - y'|)
    (u v : ℝ → Fin m → ℝ)
    (humeas : Measurable (fun s : Ico t M.T => u s)) (hvmeas : Measurable (fun s : Ico t M.T => v s))
    (hu : IntegrableOn (fun s => sqNorm (u s)) (Icc t M.T))
    (hv : IntegrableOn (fun s => sqNorm (v s)) (Icc t M.T))
    (X₁ X₂ : ℝ → ℝ → Ω → ℝ)
    (hX₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M.IsUniqueWealthFrom P F W
      (spike t ε a (fun s y => y • u s + v s)) t x (X₁ ε))
    (hX₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M.IsUniqueWealthFrom P F W
      (spike t ε (fun _ _ => a t x) (fun s y => y • u s + v s)) t x (X₂ ε)) :
    (∀ p : ℝ, 1 ≤ p → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      MemLp (X₁ ε M.T) (ENNReal.ofReal p) P ∧ MemLp (X₂ ε M.T) (ENNReal.ofReal p) P) ∧
    Tendsto (fun ε => ∫ ω, (X₁ ε M.T ω - X₂ ε M.T ω) / ε ∂P) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ∫ ω, (X₁ ε M.T ω - X₂ ε M.T ω) * X₁ ε M.T ω / ε ∂P) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ∫ ω, (X₁ ε M.T ω - X₂ ε M.T ω) * X₂ ε M.T ω / ε ∂P) (𝓝[>] 0) (𝓝 0) ∧
    (∀ p : ℝ, 1 ≤ p → Tendsto
      (fun ε => ∫ ω, (|X₁ ε M.T ω - X₂ ε M.T ω| / Real.sqrt ε) ^ p ∂P) (𝓝[>] 0) (𝓝 0)) ∧
    Tendsto (fun ε => variance (fun ω => X₁ ε M.T ω - X₂ ε M.T ω) P / ε) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => covariance (fun ω => X₁ ε M.T ω - X₂ ε M.T ω) (X₁ ε M.T) P / ε)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => covariance (fun ω => X₁ ε M.T ω - X₂ ε M.T ω) (X₂ ε M.T) P / ε)
      (𝓝[>] 0) (𝓝 0) := by sorry

end DynTargetMV
