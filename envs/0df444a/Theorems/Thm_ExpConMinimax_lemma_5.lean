-- Prove2me | Theorems.Thm_ExpConMinimax_lemma_5
-- name    : ExpConMinimax.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:53:19.31713+00:00
-- url     : https://prove2.me/theorems/c721726b-ccf6-44ad-a1f6-77eaa1337711
-- title:
--   Lemma 5 (corrected: $(\mathbb E\|\gamma\|^2)^{1/2},(\mathbb E\|\lambda\|^2)^{1/2}$ for $\mathbb E\|\gamma\|,\mathbb E\|\lambda\|$; sign in $V_t$) — expected noise terms (3.11)
-- statement:
--   Assumptions 2.1 and 2.2 and the standing assumptions of the problem are in force (§3, p.11). Let $(x_t,y_t,\gamma_t,\lambda_t)$ be a run of Algorithm 1 with constant positive step sizes $\eta_0,\kappa_0,\alpha_0,\beta_0$, driven by i.i.d. oracle samples. Let $(x,y,\gamma,\lambda)$ be a **random** reference point with values in $\mathcal X\times\mathcal Y\times\mathbb R^{m_1}_+\times\mathbb R^{m_2}_+$ and $\mathbb E\|x\|^2,\mathbb E\|y\|^2,\mathbb E\|\gamma\|^2,\mathbb E\|\lambda\|^2<\infty$. Then for every $K\ge1$ the sums $\sum_{t<K}U_t(x,\gamma)$, $\sum_{t<K}V_t(y,\lambda)$ are integrable and
--   $$\mathbb E\Big[\sum_{t=0}^{K-1}U_t(x,\gamma)\Big]\le\frac{\eta_0}2\mathbb E\|x\|^2+\sum_{t=0}^{K-1}\frac4{\eta_0}\big(C_f^2+C_h^2\mathbb E\|\gamma_{t+1}\|^2\big)+\sqrt K\big(\mathbb E\|\gamma\|^2\big)^{1/2}\sigma_h+\frac{K\sigma_h^2}{2\beta_0},$$
--   $$\mathbb E\Big[\sum_{t=0}^{K-1}V_t(y,\lambda)\Big]\le\frac{\kappa_0}2\mathbb E\|y\|^2+\sum_{t=0}^{K-1}\frac4{\kappa_0}\big(C_f^2+C_g^2\mathbb E\|\lambda_{t+1}\|^2\big)+\sqrt K\big(\mathbb E\|\lambda\|^2\big)^{1/2}\sigma_g+\frac{K\sigma_g^2}{2\alpha_0}.$$
--
--   The paper prints $\sqrt K\,\mathbb E[\|\gamma\|]\sigma_h$ and $\sqrt K\,\mathbb E[\|\lambda\|]\sigma_g$, which rest on the false Lemma 21(a); the first line fails for $d_x=m_1=1$, $F\equiv H\equiv0$, zero sampled subgradients, $h(x,\xi)=\xi$ with $\xi=-2$ w.p. $1/3$ and $1$ w.p. $2/3$, $K=1$, $x=0$, $\gamma=c\,\mathbf 1\{\xi^1_0=-2\}$ and $c$ large.
--
--   $V_t$ is the same object as in Lemma 4, with the corrected sign of its first term; the bound does not depend on that sign (its proof is the proof of the first line with $\delta_t$ replaced by $-\delta_t$ in Lemma 21).
--
--   With Lemma 4 this bounds the expected cumulative gap (Theorem 6).
--
--   Differences from the source:
--   - correction: $\sqrt K\,\mathbb E[\|\gamma\|]\sigma_h$ and $\sqrt K\,\mathbb E[\|\lambda\|]\sigma_g$ → $\sqrt K(\mathbb E\|\gamma\|^2)^{1/2}\sigma_h$ and $\sqrt K(\mathbb E\|\lambda\|^2)^{1/2}\sigma_g$; reason: the printed first line is false: $h(x,\xi)=\xi\in\{-2,1\}$ w.p. $1/3,2/3$, all else $0$, $K=1$, $\gamma=c\mathbf 1\{\xi^1_0=-2\}$ gives $\mathbb EU_0-\mathrm{RHS}=c(2-\sqrt2)/3-4(1+\mathbb E\gamma_1^2)/\eta_0>0$ for large $c$
--   - correction: $V_t$ of (3.10) with first term $(\widetilde\nabla_yL-\widetilde\nabla_y\mathcal L)^\top(y-y_t)$ → first term $(\widetilde\nabla_y\mathcal L-\widetilde\nabla_yL)^\top(y-y_t)$; reason: $V_t$ is one object in (3.9) and (3.11), and the printed sign makes (3.9) false (see Lemma 4); the second line of (3.11) holds with either sign, since Lemma 21 applies to $-\delta_t$ as well
--   - generalization: $F=\mathbb E_\omega f$, $H=\mathbb E_\xi h$, $G=\mathbb E_\zeta g$ → $F$, $H$, $G$ are given functions; $f,h,g$ enter only through the oracle maps, whose means are tied to $F,H,G$ by Assumptions 2.1–2.2; reason: every instance of the paper (with $F:=\mathbb E f$, etc.) is an instance of the Lean statement
--   - generalization: $\widetilde\nabla_xF(x,y)\in\partial_xF(x,y)$, $\widetilde\nabla H(x)\in\partial H(x)$, $\widetilde\nabla G(y)\in\partial G(y)$; convexity of $F(\cdot,y)$, $-F(x,\cdot)$, $H_i$, $G_j$ → subgradient (supergradient for $F(x,\cdot)$) inequalities and convexity required only on $\mathcal X$, resp. $\mathcal Y$; reason: weaker hypotheses: global subgradients and global convexity imply them
--   - generalization: $\mathbb E\|\widetilde\nabla h(x,\xi)\|^2\le C_h^2$ (matrix norm unspecified) → the operator norm of the sampled Jacobian; reason: the operator norm is at most the Frobenius norm, so the hypothesis is weaker and covers both readings
--   - encoding: $\operatorname{argmin}$/$\operatorname{argmax}$ updates of Algorithm 1 → each new iterate is feasible and at least as good as every feasible competitor; reason: the objectives are strongly convex/concave, so this characterizes the unique iterate
--   - encoding: step sizes constant "for all $1\le t\le N$" (resp. $t=1,\dots,N$) → one constant value in every iteration $t\ge 0$; reason: Algorithm 1 iterates $t=0,\dots,N-1$ and the bounds use the same value at $t=0$; constant step sizes are meant
--   - encoding: $K=1,\dots,N$ for a run of horizon $N$ → every $K\ge1$; reason: the run is defined for every $t$, and $N=K$ is a horizon
--   - encoding: two independent oracle queries per iteration, independent across iterations → the sample tuples $S_t=(\omega^1_t,\omega^2_t,\xi^1_t,\xi^2_t,\zeta^1_t,\zeta^2_t)$ are independent across $t$, each with law $P_\omega\otimes P_\omega\otimes P_\xi\otimes P_\xi\otimes P_\zeta\otimes P_\zeta$; reason: the paper's sampling model (pp.8, 10)
--   - encoding: oracle outputs are random vectors → the oracle maps are jointly (strongly) measurable in the query point and the sample; reason: needed for the iterates to be random variables; the paper treats them as such
--   - encoding: $\mathbb E[\|\cdot\|^2]<+\infty$ → `MemLp · 2` (measurable and square integrable); reason: a finite second moment presupposes a random variable
--   - encoding: expectations of the bounded quantities → integrability of each integrand is added to the conclusion; reason: so the Bochner integrals are the expectations (no junk value $0$)
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Lemma 5, (3.11), p.13 (proof App. B.4, pp.30–31)

import Mathlib
import Definitions.Def_ExpConMinimax_Assumption21
import Definitions.Def_ExpConMinimax_Assumption22
import Definitions.Def_ExpConMinimax_IsRun
import Definitions.Def_ExpConMinimax_SampleModel
import Definitions.Def_ExpConMinimax_Ut

namespace ExpConMinimax

open MeasureTheory

/-- **Lemma 5** (corrected: `E‖γ‖`, `E‖λ‖` replaced by `(E‖γ‖²)^{1/2}`, `(E‖λ‖²)^{1/2}`; sign of
the first term of `Vₜ`).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Lemma 5, p.13 (Assumptions 2.1 and 2.2 hold throughout §3, p.11):

"Under the same settings as in Lemma 4, for any `(x,y,γ,λ) ∈ X × Y × ℝ^{m₁}_+ × ℝ^{m₂}_+`
satisfying `E[‖x‖²] < +∞, E[‖y‖²] < +∞, E[‖γ‖²] < +∞, and E[‖λ‖²] < +∞`, it holds that
`E[∑_{t=0}^{K−1} Uₜ(x,γ)] ≤ η₀/2 E[‖x‖²] + ∑_{t=0}^{K−1} 4/ηₜ (C_f² + C_h²E[‖γₜ₊₁‖²]) + √K E[‖γ‖]σ_h
  + Kσ_h²/(2β₀)`,
`E[∑_{t=0}^{K−1} Vₜ(y,λ)] ≤ κ₀/2 E[‖y‖²] + ∑_{t=0}^{K−1} 4/κₜ (C_f² + C_g²E[‖λₜ₊₁‖²]) + √K E[‖λ‖]σ_g
  + Kσ_g²/(2α₀)`. (3.11)"

The reference point `(x,y,γ,λ)` is random (it may depend on the trajectory, p.12 and p.14).
Stated with `√K (E‖γ‖²)^{1/2} σ_h` and `√K (E‖λ‖²)^{1/2} σ_g`. **The printed first line is
false**: `d_x = m₁ = 1`, `F ≡ H ≡ 0`, all sampled subgradients `0`, `h(x,ξ) = ξ` with `ξ = −2`
w.p. `1/3` and `1` w.p. `2/3` (`σ_h² = 2`), `K = 1`, `x = 0`, `γ = c·𝟙{ξ¹₀ = −2}`: then
`E U₀ − RHS = c(2 − √2)/3 − 4(1 + Eγ₁²)/η₀ > 0` for large `c`.

`Vₜ` is `ExpConMinimax.Vt`, the same object as in Lemma 4, whose first term has the sign opposite
to the printed (3.10) (see `lemma_4`). The proof of the second line of (3.11) does not see that
sign: it is the proof of the first line with `δₜ` replaced by `−δₜ` in Lemma 21.

**Formalization Note.** `(Ω, Pr)` carries the i.i.d. samples (`SampleModel`); the oracle maps
are jointly measurable. The random reference point satisfies `x(ω) ∈ X`, `y(ω) ∈ Y`,
`γ(ω) ≥ 0`, `λ(ω) ≥ 0` for every `ω` and is square integrable (`MemLp · 2`). Constant step sizes
in every iteration; every `K ≥ 1`. The integrability of `∑ₜ Uₜ` and `∑ₜ Vₜ` is part of the
conclusion, so the Bochner integrals are the expectations. -/
theorem lemma_5 {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω]
    [MeasurableSpace Sξ] [MeasurableSpace Sζ] (P : Problem dx dy m₁ m₂)
    (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (Cf Ch σh Cg σg : ℝ) (hP : P.Standing)
    (hA21 : Assumption21 P O Cf) (hA22 : Assumption22 P O Ch σh Cg σg)
    (hOm : O.IsMeasurable)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (S : ℕ → Ω → SampleTuple Sω Sξ Sζ) (hS : SampleModel O Pr S) (η₀ κ₀ α₀ β₀ : ℝ)
    (x₀ : Vec dx) (y₀ : Vec dy) (γ₀ : Vec m₁) (lam₀ : Vec m₂)
    (x : ℕ → Ω → Vec dx) (y : ℕ → Ω → Vec dy) (γ : ℕ → Ω → Vec m₁) (lam : ℕ → Ω → Vec m₂)
    (hrun : IsRun P O S (fun _ => η₀) (fun _ => κ₀) (fun _ => α₀) (fun _ => β₀)
      x₀ y₀ γ₀ lam₀ x y γ lam)
    (u : Ω → Vec dx) (v : Ω → Vec dy) (g : Ω → Vec m₁) (l : Ω → Vec m₂)
    (hu : ∀ ω, u ω ∈ P.X) (hv : ∀ ω, v ω ∈ P.Y) (hg : ∀ ω, IsNonneg (g ω))
    (hl : ∀ ω, IsNonneg (l ω))
    (hu2 : MemLp u 2 Pr) (hv2 : MemLp v 2 Pr) (hg2 : MemLp g 2 Pr) (hl2 : MemLp l 2 Pr) :
    ∀ K : ℕ, 1 ≤ K →
      (Integrable (fun ω => ∑ t ∈ Finset.range K,
          Ut P O S (fun _ => η₀) (fun _ => β₀) x y γ t ω (u ω) (g ω)) Pr ∧
        ∫ ω, ∑ t ∈ Finset.range K,
            Ut P O S (fun _ => η₀) (fun _ => β₀) x y γ t ω (u ω) (g ω) ∂Pr ≤
          η₀ / 2 * ∫ ω, ‖u ω‖ ^ 2 ∂Pr
            + ∑ t ∈ Finset.range K, 4 / η₀ * (Cf ^ 2 + Ch ^ 2 * ∫ ω, ‖γ (t + 1) ω‖ ^ 2 ∂Pr)
            + Real.sqrt K * Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂Pr) * σh + K * σh ^ 2 / (2 * β₀)) ∧
      (Integrable (fun ω => ∑ t ∈ Finset.range K,
          Vt P O S (fun _ => κ₀) (fun _ => α₀) x y lam t ω (v ω) (l ω)) Pr ∧
        ∫ ω, ∑ t ∈ Finset.range K,
            Vt P O S (fun _ => κ₀) (fun _ => α₀) x y lam t ω (v ω) (l ω) ∂Pr ≤
          κ₀ / 2 * ∫ ω, ‖v ω‖ ^ 2 ∂Pr
            + ∑ t ∈ Finset.range K, 4 / κ₀ * (Cf ^ 2 + Cg ^ 2 * ∫ ω, ‖lam (t + 1) ω‖ ^ 2 ∂Pr)
            + Real.sqrt K * Real.sqrt (∫ ω, ‖l ω‖ ^ 2 ∂Pr) * σg + K * σg ^ 2 / (2 * α₀)) := by sorry

end ExpConMinimax
