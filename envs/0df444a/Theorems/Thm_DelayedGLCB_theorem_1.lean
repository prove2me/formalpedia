-- Prove2me | Theorems.Thm_DelayedGLCB_theorem_1
-- name    : DelayedGLCB.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:27:21.490833+00:00
-- url     : https://prove2.me/theorems/723e4f43-1a2b-4665-94f6-a886e3cc8b45
-- title:
--   Theorem 1 — DUCB-GLCB has regret at most (16) with probability at least $1-5\delta$ (corrected: envelope $\xi$ on $[0,\infty)$)
-- statement:
--   Let $M>0$, $\mu\in\mathbb R$, $\sigma_0>0$, $\hat\sigma>0$, $\sigma>0$ and $\kappa>0$. There is a constant $C>0$, depending only on these, with the following property.
--
--   Let $q\ge0$, $1\le d\le T$, $K\ge1$, $\delta\in(0,1)$, $L_g,M_g\in\mathbb R$, $\theta^*\in\mathbb R^d$, a non-decreasing link $g$ and a distribution $\xi$. Take any probability space carrying contexts $x_{t,a}$, rewards $y_{t,a}$, delays $D_t$ and exploration draws $\alpha_t$ such that:
--
--   1. the round model holds (bounded data, fresh i.i.d. rounds, uniform exploration draws);
--   2. Assumption 1 holds with $\sigma_0,\kappa,L_g,M_g$;
--   3. the rewards satisfy the sub-Gaussian model (2)–(3) with parameter $\hat\sigma$;
--   4. the delays have tail envelope $(\xi,\mu,M)$ with exponent $q$ and scale $\sigma$ (Assumption 2);
--   5. each $D_t$ is independent of the earlier delays and of $(x_s,a_s,y_{s,a_s})_{s\le t}$, where $a_s$ are the arms DUCB-GLCB plays.
--
--   Run DUCB-GLCB with $\tau=\lceil C(d+\log(1/\delta))\rceil$, the width $\beta_t$ of Algorithm 1, any estimator returning a root of (5) whenever one exists, and any arg max tie-break (both measurable). Then
--   $$
--   P\big(R_T>B_{16}\big)\le5\delta,
--   $$
--   where $B_{16}$ is the right-hand side of (16), with $\sigma_G=\sigma\sqrt{2+q}$ and $C_3=2\sigma^2+1$.
--
--   This is the paper's main guarantee. Delays affect the regret only through the additive terms involving $\mu+M$ and $\sigma_G$; the leading term $d\sqrt T\log T$ is that of the undelayed problem.
--
--   Differences from the source:
--   - correction: ξ a distribution with mean µ < ∞ → ξ a probability measure on [0, ∞) with finite mean µ; reason: over all of ℝ the statement is false: ξ = point mass at −100 (µ = −100), M = 10, σ = 0.1, q = 0, D_t ≡ 9.5 satisfy every clause of Assumption 2, yet G_t ≥ 9 for t ≥ 10 while the right side of (6) is negative; ξ is introduced as an envelope delay distribution (p.6) and the proof uses E[D_t] ≤ µ + M (p.23)
--   - reading: β_t = (σ̂/κ)√((d/2) log(1 + 2(t−G_t)/d) + log(1/δ)) + G_t → … + √G_t; reason: Algorithm 1 (line 5, p.7), the proof (37) and its use on p.26, and Theorems 3 and 5 all have √G_t, and (16) is derived from √G*_T (p.27)
--   - generalization: conditional law of Y_t given X_t from the exponential family (1) → the reward model (2)–(3): y_{t,a} ∈ [0,1] with conditionally σ̂-sub-Gaussian noise around g(x'_{t,a}θ*) given x_t, and g non-decreasing; reason: (1) implies each condition (ġ = m̈ = V(Y|X) ≥ 0 and the sub-Gaussian bound, p.5), and Remark 1 states the analysis for (2)–(3)
--   - reading: x_t drawn iid from γ; D_t independent of {D_s}_{s≤t−1} and {x_s, y_{s,a_s}, a_s}_{s≤t} → the round model (round-t data independent of all earlier data and delays, identically distributed) and the literal p.5 independence of D_t about the arms DUCB-GLCB plays; reason: without freshness the literal sentence allows D_s to depend on a later context; the noise condition (3) on H_t^0 follows from the per-arm condition given x_t under freshness
--   - reading: randomly choose α_t ∈ [K] → α_t uniform on [K] and independent of (x_t, y_t); reason: Assumption 1's average (1/K)Σ_a makes the exploration design well conditioned only under the uniform draw
--   - generalization: κ := inf_{‖x‖≤1, ‖θ−θ*‖≤1} ġ(x'θ) → any κ > 0 with κ ≤ ġ(x'θ) on that set; reason: the infimum is one such κ
--   - reading: the MLE θ̂_t solving (5) → any measurable estimator of the complete tuples returning a root of (5) whenever one exists (arbitrary otherwise); reason: (5) need not have a root; requiring one always would make the hypotheses unsatisfiable
--   - encoding: arg max in Step 6 → a measurable deterministic tie-break returning a maximizer; reason: a measurable arg max rule exists (first maximizer)
--   - reading: Fix any δ; T rounds; d, K → δ ∈ (0, 1), 1 ≤ d ≤ T, K ≥ 1; reason: log(1/δ) sits under a root and 1 − 5δ is meaningful only for δ < 1; log(T/d) and √(Td log(T/d)) need T ≥ d
--   - encoding: τ := C(d + log(1/δ)) → τ = ⌈C(d + log(1/δ))⌉; reason: τ counts rounds
--   - reading: G_t = Σ_{s=1}^{t−1} 𝕀{s + D_s ≥ t} and T_t = {s ≤ t − 1 : s + D_s ≤ t − 1} → G_t = #{s ∈ [1, t − 1] : s + D_s > t − 1} = (t − 1) − |T_t|; reason: Algorithm 1 (lines 2, 7) sets G_t = (t − 1) − |T_t|; for a fractional delay the printed sum and this count disagree, and the reward of round s is read as arriving at the end of round ⌈s + D_s⌉; for integer delays the two coincide
--   - reading: P(D − µ ≥ x) ≤ exp(−x^{1+q}/(2σ²)) → the inequality for every x ≥ 0, with x^{1+q} the real power; reason: x^{1+q} is not defined for negative x when q is not an integer, and for x < 0 the bound is not meant
--   - encoding: λ_min(A), the smallest eigenvalue → lambdaMin A, the infimum of v'Av over unit vectors; reason: equal for symmetric matrices, which are the only ones it is applied to
--   - encoding: ‖x‖_{V_t^{-1}} → V_t^{-1} is Matrix.inv (0 when V_t is singular); reason: Lean's total inverse; on the event the proof uses, V_t is invertible
--   - encoding: random variables D_t (and features) → measurable functions, non-negativity and the unit-ball bound at every outcome; reason: standing convention of probability; no instance of the paper is excluded up to null-set modification
--   - encoding: with probability (at least) 1 − 5δ, the bound holds → P(the bound fails) ≤ 5δ; reason: complement form; for measurable events the two are the same
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Theorem 1, (16), p.10

import Mathlib
import Definitions.Def_DelayedGLCB_Env
import Definitions.Def_DelayedGLCB_TailEnvelope
import Definitions.Def_DelayedGLCB_Assumption1
import Definitions.Def_DelayedGLCB_DUCB
import Definitions.Def_DelayedGLCB_bound16

universe u

namespace DelayedGLCB

open MeasureTheory ProbabilityTheory

/-- **Theorem 1 (high-probability regret of DUCB-GLCB).**
Blanchet, Xu, Zhou, *Delay-Adaptive Learning in Generalized Linear Contextual Bandits*,
arXiv:2003.05174v1, Theorem 1, (16), p.10: "Assume Assumptions 1-2. Fix any `δ`. There exists a
universal constant `C := C(C₁, C₂, M, µ, σ₀, σ̂, σ, κ) > 0`, such that if we run DUCB-GLCB with
`τ := C(d + log(1/δ))` and `β_t = (σ̂/κ)√((d/2) log(1 + 2(t−G_t)/d) + log(1/δ)) + G_t`, then, with
probability at least `1 − 5δ`, the regret of the algorithm is upper bounded by (16)."

For all `M > 0`, `µ`, `σ₀ > 0`, `σ̂ > 0`, `σ > 0`, `κ > 0` there is `C > 0` such that for every
`q ≥ 0`, `1 ≤ d ≤ T`, `K ≥ 1`, `δ ∈ (0,1)`, `L_g`, `M_g`, `θ*`, `g`, `ξ`, every probability space and
environment satisfying the round model, Assumption 1 with `g` non-decreasing, the reward model (2)–(3), the tail envelope
`(ξ, µ, M)` and the independence of the delays (p.5), every root-selecting estimator and every argmax
tie-break (both measurable): running DUCB-GLCB with `τ = ⌈C(d + log(1/δ))⌉` and the width
`β_t` of Algorithm 1 gives `P(R_T > bound (16)) ≤ 5δ`.

**Formalization Note.** (1) `C` is chosen after `M, µ, σ₀, σ̂, σ, κ` and before everything else,
as printed. (2) `β_t` carries `√G_t` (Algorithm 1, line 5; the proof (37)); the statement's
"`+ G_t`" is read as `+ √G_t`. (3) `τ` is rounded up to an integer. (4) The envelope `ξ` lives on
`[0, ∞)` (see `TailEnvelope`). (5) Rounds are `1, …, T`; delays are real, with
`s ∈ T_t ↔ s + D_s ≤ t − 1`. (6) The estimator sees only the complete tuples and returns a root of
(5) whenever one exists; `V_t^{-1}` is `Matrix.inv`. (7) `κ` is any positive lower bound of `ġ` on
the set of Assumption 1; `g` is non-decreasing, as under the exponential family (1)
(`ġ = m̈ = V(Y|X) ≥ 0`, p.5). (8) The independence hypothesis is about the arms the algorithm plays. -/
theorem theorem_1 (M μ σ₀ σhat σ κ : ℝ) (hM : 0 < M) (hσ₀ : 0 < σ₀) (hσhat : 0 < σhat)
    (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℝ) (d K T : ℕ) (δ Lg Mg : ℝ) (θstar : Fin d → ℝ) (g : ℝ → ℝ) (ξ : Measure ℝ)
        {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : Env Ω d K)
        (est : Estimator d) (tie : (Fin K → ℝ) → Fin K),
        0 ≤ q → 1 ≤ d → 1 ≤ K → d ≤ T → 0 < δ → δ < 1 →
        RoundModel P E T →
        Assumption1 P E T θstar g σ₀ κ Lg Mg → Monotone g →
        RewardModel P E T θstar g σhat →
        TailEnvelope P E.D T ξ μ M q σ →
        IsRootSelecting g est → (∀ n, Measurable (est n)) →
        IsArgmaxSelector tie → Measurable tie →
        let A : DUCB d K :=
          { g := g, κ := κ, σhat := σhat, δ := δ,
            τ := ⌈C * ((d : ℝ) + Real.log (1 / δ))⌉₊, est := est, tie := tie }
        DelayIndependent P E (fun t ω => action A E ω t) T →
        P {ω | bound16 μ M σ q σhat κ Lg d T δ A.τ
            < regret E g θstar (fun t ω => action A E ω t) T ω} ≤ ENNReal.ofReal (5 * δ) := by sorry

end DelayedGLCB
