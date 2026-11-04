-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_1
-- name    : ChurnServiceMode.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:43.14119+00:00
-- url     : https://prove2.me/theorems/bfe7a1c4-d38c-4738-a867-db8c1a3a2d5c
-- title:
--   Lemma 1 — interval policies have solutions; Itô–Tanaka formula (corrected: uniqueness in law only for nondegenerate Safe intervals; $f″$ locally integrable)
-- statement:
--   1. For every interval policy $\pi$ and every starting satisfaction $x$, there is a control system started at $x$ that follows $\pi$, and its reward $Y$, satisfaction $H$ and survival $S$ processes are adapted continuous semimartingales. If moreover no Safe interval of $\pi$ is a single point, all such systems give $H$ the same law.
--   2. For every control system and every function $f$ that is continuously differentiable on $\mathbb R$ and twice continuously differentiable on $\mathbb R\setminus E$ for some countable set $E$, with $f''$ locally integrable, $f(H_t)$ is an adapted continuous semimartingale and, almost surely, for all $t\ge0$,
--   $$f(H_t)=f(x)+\int_0^t(\mu_{u_s}-H_s)f'(H_s)\,ds+\int_0^t\sigma_{u_s}f'(H_s)\,dB_s+\frac12\int_0^t\sigma_{u_s}^2f''(H_s)\mathbb 1\{H_s\notin E\}\,ds .$$
--
--   Part 2 is the Itô–Tanaka formula (10) that the verification argument applies to the candidate value function, which is $C^1$ but not $C^2$.
--
--   **Formalization Note** The law of $H$ is the image measure of $P$ under $\omega\mapsto(t\mapsto H_t(\omega))$ on the product σ-algebra; $Y$ and $S$ are functionals of the path of $H$. The term $f''(H_s)\mathbb 1\{H_s\notin E\}$ is $0$ on $E$ (footnote 7).
--
--   Differences from the source:
--   - correction: part 1: the processes are "specified uniquely in law" for every interval policy → uniqueness in law of H only when every Safe interval has nonempty interior (SafeIntervalsNondegenerate); reason: a single-point Safe interval {y} (allowed by Definition 2; the paper's own case θb = q, p.10) has σ = 0 and drift µS − y ≠ 0 at y with σR > 0 on both sides; the SDE then has sticky-skew solutions spending positive time at y for every stickiness ρ ≥ 0 (ρ = 0 is the plain O-U process), with different laws
--   - correction: part 2: f C¹ on ℝ and C² on ℝ∖E → additionally f″ locally integrable (LocallyIntegrable (deriv (deriv f))); reason: counterexample: π ≡ R (an interval policy), x = 0, E = {0}, f(x) = ∫₀ˣ y² sin(1/y²) dy; f is C¹ and C² off 0 but ∫₀^ε |f″| = ∞, so by the occupation-times formula ∫₀ᵗ σR²|f″(H_s)| ds = ∞ a.s. and the last integral of (10) does not exist
--   - generalization: part 2 for an interval policy π → for every control system; reason: p.7: "the Itô-Tanaka formula in Eq. (10) holds … under any admissible policy", and the proof of Proposition 2 uses it that way; interval-policy systems are control systems
--   - reading: "exist and are F-adapted semimartingales specified uniquely in law" → weak existence: some filtered probability space carrying a Brownian motion and a solution; reason: "specified uniquely in law" refers to weak solutions; the construction via Salins–Spiliopoulos is a weak one
--   - encoding: f′, f″; uniqueness in law of (Y, H, S) → deriv f, deriv (deriv f); equality of the laws of the path of H; reason: Y and S are measurable functionals of the path of H
--   - encoding: time t ≥ 0; continuous paths → time in ℝ≥0; every path of H and B continuous; reason: standard convention for continuous diffusions; same instances up to modification
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - reading: interval policy (Definition 2): "a countable number of alternating Risky and Safe intervals", Safe at each boundary point → IsIntervalPolicy π: the Risky set {π = R} is open and its frontier meets every bounded interval in finitely many points (a Safe interval may be a single point); reason: alternating intervals listed in order have no accumulating endpoints, and the proof of Lemma 1 (p.21) builds the process "inductively on the number of pieces of intervals"; openness of the Risky set is "Safe at each boundary point"
--   - reading: "twice continuously differentiable on ℝ∖E" for a countable E (ℝ∖E need not be open); V′, V″ → deriv V differentiable at every point off E and deriv (deriv V) continuous on Eᶜ (relative topology); V′ = deriv V, V″ = deriv (deriv V); reason: the pointwise reading of C² on a set that need not be open; when E is closed (for W*, E ⊆ {θG, q, θb}) it is C² on the open set ℝ∖E
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 1 with display (10) and footnote 7, p.7 (PDF p.7); remark after (10), p.7

import Mathlib
import Definitions.Def_ChurnServiceMode_ControlSystem

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Lemma 1** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.7; corrected: uniqueness in law only for nondegenerate Safe intervals,
and display (10) with a locally integrable `f″`).
1. For every interval policy `π` and every `x`, a `π`-feedback control system started at `x`
   exists, and its reward `Y`, satisfaction `H` and survival `S` processes are adapted continuous
   semimartingales. If moreover every Safe interval of `π` is nondegenerate, all `π`-feedback
   systems started at `x` give `H` the same law.
2. For every control system and every `f` that is continuously differentiable on `ℝ`, twice
   continuously differentiable on `ℝ ∖ E` for a countable `E`, with `f″` locally integrable,
   `f(H_t)` is an adapted continuous semimartingale and, almost surely, for every `t` (display (10)):
   `f(H_t) = f(x) + ∫₀ᵗ (μ_{u_s} − H_s) f′(H_s) ds + ∫₀ᵗ σ_{u_s} f′(H_s) dB_s
     + ½ ∫₀ᵗ σ²_{u_s} f″(H_s) 1{H_s ∉ E} ds`.

**Formalization Note.** The law of `H` is the image of `P` under `ω ↦ (t ↦ H_t(ω))` on the product
σ-algebra of `ℝ≥0 → ℝ` (a measurable map since `H` is adapted). `∫ σ f′(H) dB` is characterized by
the published `HasMartingaleIntegral`. Footnote 7's convention `f″(H_s)1{H_s ∉ E} = 0` on `E` is
the indicator of `ℝ ∖ E` applied to `f″`. Part 2 is stated for every control system (p.7: "the Itô-Tanaka formula in Eq.
(10) holds … under any admissible policy"). -/
theorem lemma_1 (p : Params) :
    (∀ π : ℝ → Mode, IsIntervalPolicy π → ∀ x : ℝ,
      ∃ S : ControlSystem p x, S.IsFeedback π ∧
        Nonempty (ContinuousSemimartingale S.P S.ℱ S.reward) ∧
        Nonempty (ContinuousSemimartingale S.P S.ℱ S.H) ∧
        Nonempty (ContinuousSemimartingale S.P S.ℱ S.survival)) ∧
    (∀ π : ℝ → Mode, IsIntervalPolicy π → SafeIntervalsNondegenerate π →
      ∀ (x : ℝ) (S S' : ControlSystem p x), S.IsFeedback π → S'.IsFeedback π →
        S.P.map (fun ω t => S.H t ω) = S'.P.map (fun ω t => S'.H t ω)) ∧
    (∀ (x : ℝ) (S : ControlSystem p x) (f : ℝ → ℝ) (E : Set ℝ), E.Countable →
      ContDiff ℝ 1 f → (∀ y ∉ E, DifferentiableAt ℝ (deriv f) y) →
      ContinuousOn (deriv (deriv f)) Eᶜ → LocallyIntegrable (deriv (deriv f)) →
      Nonempty (ContinuousSemimartingale S.P S.ℱ (fun t ω => f (S.H t ω))) ∧
      ∃ N : ℝ≥0 → S.Ω → ℝ,
        HasMartingaleIntegral S.P S.ℱ S.B (timeClock S.Ω)
          (fun t ω => p.sig (S.u t ω) * deriv f (S.H t ω)) N ∧
        ∀ᵐ ω ∂S.P, ∀ t : ℝ≥0, f (S.H t ω) = f x
          + clockIntegral (timeClock S.Ω)
              (fun s w => (p.mu (S.u s w) - S.H s w) * deriv f (S.H s w)) t ω
          + N t ω
          + 1 / 2 * clockIntegral (timeClock S.Ω)
              (fun s w => p.sig (S.u s w) ^ 2 *
                Set.indicator Eᶜ (deriv (deriv f)) (S.H s w)) t ω) := by sorry

end ChurnServiceMode
