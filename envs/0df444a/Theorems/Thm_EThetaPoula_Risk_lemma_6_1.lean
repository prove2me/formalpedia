-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_6_1
-- name    : EThetaPoula.Risk.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:33.943904+00:00
-- url     : https://prove2.me/theorems/95209b04-d009-4656-a982-d8611ca35362
-- title:
--   Lemma 6.1, p.23 — moment estimates of $\bar\theta^\lambda$ (corrected: the finiteness in (ii) needs $E[|\theta_0|^{2p}]<\infty$)
-- statement:
--   Let Assumptions 1–4 hold and $0<\varepsilon<1$.
--
--   1. For $0<\lambda\le\lambda_{1,\max}$, $n\in\mathbb N_0$, $t\in(n,n+1]$,
--   $$
--   E[|\bar\theta^\lambda_t|^2]\le(1-\lambda(t-n)a_F\kappa)(1-a_F\kappa\lambda)^nE[|\theta_0|^2]+\mathring c_0,
--   $$
--   and $\sup_{t\ge0}E[|\bar\theta^\lambda_t|^2]\le E[|\theta_0|^2]+\mathring c_0<\infty$.
--   2. For $p\in[2,\infty)\cap\mathbb N$, $0<\lambda\le\lambda_{p,\max}$, $n\in\mathbb N_0$, $t\in(n,n+1]$,
--   $$
--   E[|\bar\theta^\lambda_t|^{2p}]\le(1-\lambda(t-n)a_F\kappa^\sharp_2)(1-\lambda a_F\kappa^\sharp_2)^nE[|\theta_0|^{2p}]+\mathring c_p,\tag{40}
--   $$
--   and $\sup_{t\ge0}E[|\bar\theta^\lambda_t|^{2p}]\le E[|\theta_0|^{2p}]+\mathring c_p$.
--   3. If $F(\theta,x)=\hat F(\theta)$ for all $\theta,x$, then (40) holds for $p\in[2,\infty)\cap\mathbb N$ with $E[(1+|X_0|)^{2p\rho}]<\infty$ and $0<\lambda\le\hat\lambda_{\max}$ of (41).
--
--   The constants are those of (85), (110), (129). The estimates are uniform in time, which is what allows a bound that does not grow with $n$.
--
--   **Formalization Note** Moments are lower Lebesgue integrals with values in $[0,\infty]$, because $E[|\theta_0|^{2p}]$ may be infinite for $p>4r+2$.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - reading: $\binom{p}{\lceil p/2\rceil}$ in (129), with $\lceil a\rceil:=\lfloor a\rfloor+1$ from §1 → the ordinary ceiling $(p+1)/2$ in natural division; reason: p.38 uses the coefficient as an upper bound of every $\binom pk$, which needs the central one; the two agree for odd $p$
--   - correction: $\sup_{t\ge0}E[|\bar\theta^\lambda_t|^{2p}]\le E[|\theta_0|^{2p}]+\mathring c_p<\infty$ for every integer $p\ge2$ → the same inequality in $[0,\infty]$, and the right side is finite when $E[|\theta_0|^{2p}]<\infty$; reason: the printed finiteness is false: take $X_n\equiv0$ (every moment finite, so $\lambda_{p,\max}>0$) and $\theta_0$ with $E[|\theta_0|^{8r+4}]<\infty=E[|\theta_0|^{8r+6}]$ (Assumption 1 holds); at $p=4r+3$ and $t=0$ the supremum is $E[|\theta_0|^{2p}]=\infty$
--   - encoding: (iii) for every integer $p\ge2$ and $0<\lambda\le\hat\lambda_{\max}$ → (iii) for those $p$ with $E[(1+|X_0|)^{2p\rho}]<\infty$; reason: $\hat\lambda_{\max}$ does not involve $p$; when $E[(1+|X_0|)^{2p\rho}]=\infty$ the paper's $\mathring c_p$ is $+\infty$ and (40) is trivial, while in Lean that moment would be the Bochner junk value $0$; no nontrivial instance is excluded
--   - encoding: $E[\cdot]$ of nonnegative variables, possibly $+\infty$ → lower Lebesgue integrals, with the real factors through `ENNReal.ofReal`; reason: a Bochner integral of a non-integrable function is $0$; the prefactors are nonnegative in the stated range of $\lambda$
--   - encoding: no $\epsilon$ in these constants → $\epsilon$ is a free argument of `Model.params`; reason: the constants read here do not involve it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma 6.1, (40), (41), p.23

import Mathlib
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsInterpolation
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma 6.1**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.23: under Assumptions 1–4,
the moment estimates of the interpolation `θ̄^λ` of (39).

**Formalization Note.** The moments are `∫⁻`, values in `[0, ∞]`, because `E[|θ₀|^{2p}]` may be
infinite for `p > 4r + 2`. If `E_{2pρ} = ∞` then `λ_{p,max} = 0`, so clause (ii) is vacuous, as in the
paper. The clause `sup_{t≥0} E[|θ̄^λ_t|^{2p}] < ∞` of (ii) is stated under `E[|θ₀|^{2p}] < ∞`, which
Assumption 1 gives for `p ≤ 4r + 2`; the printed `< ∞` is false without it (corrected). In (iii),
`λ̂_max` does not involve `p`, so the clause carries `E_{2pρ} < ∞`: when `E_{2pρ} = ∞` the paper's
`c̊_p` is `+∞` and (40) is trivial, while in Lean `E_{2pρ}` would be the Bochner junk `0`. The constants of this lemma do not involve `ϵ`. -/
theorem lemma_6_1 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (ϵ : ℝ) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B) :
    let K := S.params C β ϵ
    -- (i)
    (∀ (lam : ℝ), 0 < lam → lam ≤ K.lamMaxP 1 → ∀ θb : ℝ≥0 → Ω → Eucl d,
      S.IsInterpolation B lam β ε θb →
      (∀ (n : ℕ) (t : ℝ≥0), (n : ℝ≥0) < t → t ≤ n + 1 →
        ∫⁻ ω, ‖θb t ω‖ₑ ^ 2 ∂S.P ≤
          ENNReal.ofReal ((1 - lam * ((t : ℝ) - n) * K.aF * K.kappa)
              * (1 - K.aF * K.kappa * lam) ^ n) * ∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ 2 ∂S.P
            + ENNReal.ofReal K.c0ring) ∧
      (⨆ t : ℝ≥0, ∫⁻ ω, ‖θb t ω‖ₑ ^ 2 ∂S.P) ≤
          ∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ 2 ∂S.P + ENNReal.ofReal K.c0ring ∧
      ∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ 2 ∂S.P + ENNReal.ofReal K.c0ring < ⊤) ∧
    -- (ii)
    (∀ (p : ℕ), 2 ≤ p → ∀ (lam : ℝ), 0 < lam → lam ≤ K.lamMaxP p → ∀ θb : ℝ≥0 → Ω → Eucl d,
      S.IsInterpolation B lam β ε θb →
      (∀ (n : ℕ) (t : ℝ≥0), (n : ℝ≥0) < t → t ≤ n + 1 →
        ∫⁻ ω, ‖θb t ω‖ₑ ^ (2 * p) ∂S.P ≤
          ENNReal.ofReal ((1 - lam * ((t : ℝ) - n) * K.aF * K.kappaSharp)
              * (1 - lam * K.aF * K.kappaSharp) ^ n) * ∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ (2 * p) ∂S.P
            + ENNReal.ofReal (K.cRing p)) ∧
      (⨆ t : ℝ≥0, ∫⁻ ω, ‖θb t ω‖ₑ ^ (2 * p) ∂S.P) ≤
          ∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ (2 * p) ∂S.P + ENNReal.ofReal (K.cRing p) ∧
      (∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ (2 * p) ∂S.P < ⊤ →
        ∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ (2 * p) ∂S.P + ENNReal.ofReal (K.cRing p) < ⊤)) ∧
    -- (iii)
    ((∃ Fhat : Eucl d → Eucl d, ∀ θ x, S.F θ x = Fhat θ) →
      ∀ (p : ℕ), 2 ≤ p →
      Integrable (fun ω => (1 + ‖S.X 0 ω‖) ^ (2 * (p : ℝ) * S.ρ)) S.P →
      ∀ (lam : ℝ), 0 < lam → lam ≤ K.lamHat → ∀ θb : ℝ≥0 → Ω → Eucl d,
      S.IsInterpolation B lam β ε θb →
      ∀ (n : ℕ) (t : ℝ≥0), (n : ℝ≥0) < t → t ≤ n + 1 →
        ∫⁻ ω, ‖θb t ω‖ₑ ^ (2 * p) ∂S.P ≤
          ENNReal.ofReal ((1 - lam * ((t : ℝ) - n) * K.aF * K.kappaSharp)
              * (1 - lam * K.aF * K.kappaSharp) ^ n) * ∫⁻ ω, ‖S.θ₀ ω‖ₑ ^ (2 * p) ∂S.P
            + ENNReal.ofReal (K.cRing p)) := by sorry

end EThetaPoula.Risk
