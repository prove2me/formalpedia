-- Prove2me | Theorems.Thm_ChurnServiceMode_corollary_1
-- name    : ChurnServiceMode.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:54.067564+00:00
-- url     : https://prove2.me/theorems/208514fd-8d1b-4612-b07c-9c4e07c88e8a
-- title:
--   Corollary 1 — interval policies are admissible (corrected: uniqueness in law only for nondegenerate Safe intervals)
-- statement:
--   Let $\pi$ be an interval policy and $x$ a starting satisfaction level. Then:
--   1. there is a control system started at $x$ that follows $\pi$, whose reward, satisfaction and survival processes are adapted continuous semimartingales;
--   2. if no Safe interval of $\pi$ is a single point, all control systems started at $x$ that follow $\pi$ give the satisfaction process the same law;
--   3. for every control system started at $x$ that follows $\pi$, the CLV exists in $[0,\infty]$ and equals
--   $$V(x,\pi)=\mathbb E\Bigl[\int_0^\infty\mu_{\pi(H_t)}e^{-\int_0^tQ(H_s)ds}\,dt\Bigr]\qquad\text{(display (9))}.$$
--
--   Hence interval policies are admissible in the sense of Definition 1, which is what makes the policy of Theorem 1 a legitimate competitor.
--
--   Differences from the source:
--   - correction: interval policies are admissible, including uniqueness in law (Definition 1, condition 2) → uniqueness in law only when every Safe interval is nondegenerate; reason: same counterexample as Lemma 1, part 1: a single-point Safe interval admits sticky solutions with different laws
--   - reading: admissibility (Definition 1) → weak formulation: existence of a feedback ControlSystem, its processes as semimartingales, and the CLV identity (9) for every feedback system; reason: condition 3 of Definition 1 (existence of the expectation in (7)) is the existence of the CLV, a nonnegative expectation; the p.7 remark derives it through (9)
--   - reading: CLV (7): E[∫₀^∞ µ_{u_t} 1{t<T} dt + ∫₀^∞ σ_{u_t} 1{t<T} dB_t] → clv := E[∫₀^∞ µ_{u_t} 1{t<T} dt] in [0, ∞] on P ⊗ U[0,1], T as in (6) with inf ∅ = ∞; reason: footnote 6 (p.7) drops the stochastic integral as having zero expectation; the remaining term is what (9) and the proofs use
--   - encoding: time t ≥ 0; continuous paths → time in ℝ≥0; every path of H and B continuous; reason: standard convention for continuous diffusions; same instances up to modification
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - reading: interval policy (Definition 2): "a countable number of alternating Risky and Safe intervals", Safe at each boundary point → IsIntervalPolicy π: the Risky set {π = R} is open and its frontier meets every bounded interval in finitely many points (a Safe interval may be a single point); reason: alternating intervals listed in order have no accumulating endpoints, and the proof of Lemma 1 (p.21) builds the process "inductively on the number of pieces of intervals"; openness of the Risky set is "Safe at each boundary point"
--   - generalization: the CLV identity (9) for the process H^{x,π} of the policy (on the paper's filtered space, specified uniquely in law) → the CLV identity (9) for every π-feedback ControlSystem started at x, on any filtered probability space; reason: the paper's process is one such system, so the statement specializes to the paper's; it also covers solutions whose law is not unique (Lemma 1 correction)
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Corollary 1, p.8 (PDF p.8); Definition 1, p.6; display (9), p.7

import Mathlib
import Definitions.Def_ChurnServiceMode_ControlSystem

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Corollary 1** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.8; corrected: uniqueness in law only for nondegenerate Safe
intervals): any interval policy is admissible. For every interval policy `π` and every `x`:
a `π`-feedback control system started at `x` exists whose reward, satisfaction and survival
processes are adapted continuous semimartingales; if every Safe interval of `π` is nondegenerate,
all `π`-feedback systems started at `x` give `H` the same law; and the CLV of every `π`-feedback
system is the expectation in (9),
`V(x, π) = E[∫₀^∞ μ_{π(H_t)} e^{−∫₀ᵗ Q(H_s) ds} dt]`, which exists in `[0, ∞]`.

**Formalization Note.** Admissibility (Definition 1) is read in the weak formulation (reading R2):
conditions 1–2 are the existence of the system, its processes as semimartingales and their
uniqueness in law; condition 3 (existence of the expectation (7)) is the CLV identity, an
expectation of a nonnegative quantity. Uniqueness in law is asserted only when every Safe interval
has nonempty interior (Correction C3). -/
theorem corollary_1 (p : Params) (π : ℝ → Mode) (hπ : IsIntervalPolicy π) (x : ℝ) :
    (∃ S : ControlSystem p x, S.IsFeedback π ∧
      Nonempty (ContinuousSemimartingale S.P S.ℱ S.reward) ∧
      Nonempty (ContinuousSemimartingale S.P S.ℱ S.H) ∧
      Nonempty (ContinuousSemimartingale S.P S.ℱ S.survival)) ∧
    (SafeIntervalsNondegenerate π → ∀ S S' : ControlSystem p x, S.IsFeedback π →
      S'.IsFeedback π → S.P.map (fun ω t => S.H t ω) = S'.P.map (fun ω t => S'.H t ω)) ∧
    ∀ S : ControlSystem p x, S.IsFeedback π →
      S.clv = ∫⁻ ω, (∫⁻ t in Set.Ici (0 : ℝ),
        ENNReal.ofReal (p.mu (π (S.H t.toNNReal ω)) * S.survival t.toNNReal ω)) ∂S.P := by sorry

end ChurnServiceMode
