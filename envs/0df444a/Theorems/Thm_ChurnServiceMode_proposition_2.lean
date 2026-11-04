-- Prove2me | Theorems.Thm_ChurnServiceMode_proposition_2
-- name    : ChurnServiceMode.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:56.551691+00:00
-- url     : https://prove2.me/theorems/9e81af4b-2e9c-46da-9430-950e7a8c75bd
-- title:
--   Proposition 2 — verification theorem
-- statement:
--   Let $V:\mathbb R\to\mathbb R$ and let $\pi$ be a policy satisfying the six conditions of Proposition 2 (nonnegativity; $C^1$ on $\mathbb R$ and $C^2$ off a countable set $E$; bounded $V'$; the inequalities (14); $\pi$ an interval policy, Safe on $E$, with $V(H_t)$ a semimartingale and equality (15); and the limit (16)). Then $V$ is the value function and $\pi$ is optimal:
--   $$V^*(x)=V(x)\quad\text{for every }x,$$
--   a control system following $\pi$ exists from every starting point $x$, and every control system started at $x$ that follows $\pi$ attains $V^*(x)$.
--
--   Optimality holds among all admissible policies, not only interval or Markov policies.
--
--   Differences from the source:
--   - generalization: admissible policies π ∈ Π of Definition 1 (adapted control on the given filtered space, processes specified uniquely in law, integrals of (7) existing) → every ControlSystem: any filtered probability space carrying a standard Brownian motion, a progressively measurable {R,S}-valued control and a continuous adapted solution of (3) (weak formulation; uniqueness in law not required); reason: every admissible policy gives such a system (progressive measurability is what makes the integrals of (1) exist), so the class contains Π and the statement specializes to the paper's
--   - generalization: Assumption 1 (q > µS), standing since p.8 → not assumed; reason: the proof (upper bound from Conditions 1–4, attainment from Conditions 5–6) does not use it; the statement specializes to the paper's under Assumption 1
--   - reading: Conditions 5–6 for "the process V̄(H^{x,π̄}_t)" and "H^{x,π̄}" → for every π̄-feedback ControlSystem started at x; reason: weak formulation; the paper's process is unique in law where it is used
--   - reading: CLV (7): E[∫₀^∞ µ_{u_t} 1{t<T} dt + ∫₀^∞ σ_{u_t} 1{t<T} dB_t] → clv := E[∫₀^∞ µ_{u_t} 1{t<T} dt] in [0, ∞] on P ⊗ U[0,1], T as in (6) with inf ∅ = ∞; reason: footnote 6 (p.7) drops the stochastic integral as having zero expectation; the remaining term is what (9) and the proofs use
--   - encoding: time t ≥ 0; continuous paths → time in ℝ≥0; every path of H and B continuous; reason: standard convention for continuous diffusions; same instances up to modification
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - reading: interval policy (Definition 2): "a countable number of alternating Risky and Safe intervals", Safe at each boundary point → IsIntervalPolicy π: the Risky set {π = R} is open and its frontier meets every bounded interval in finitely many points (a Safe interval may be a single point); reason: alternating intervals listed in order have no accumulating endpoints, and the proof of Lemma 1 (p.21) builds the process "inductively on the number of pieces of intervals"; openness of the Risky set is "Safe at each boundary point"
--   - reading: "twice continuously differentiable on ℝ∖E" for a countable E (ℝ∖E need not be open); V′, V″ → deriv V differentiable at every point off E and deriv (deriv V) continuous on Eᶜ (relative topology); V′ = deriv V, V″ = deriv (deriv V); reason: the pointwise reading of C² on a set that need not be open; when E is closed (for W*, E ⊆ {θG, q, θb}) it is C² on the open set ℝ∖E
--   - reading: "V̄ is the value function V*, and π̄ is an optimal policy" → optimalCLV p x = V̄(x) for every x; a π̄-feedback ControlSystem exists from every x; every π̄-feedback ControlSystem started at x attains optimalCLV p x; reason: an optimal policy is one whose process attains V*; existence holds by Lemma 1 for the interval policy π̄ and keeps the attainment clause from being vacuous
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Proposition 2, displays (14)–(16), p.17 (PDF p.17)

import Mathlib
import Definitions.Def_ChurnServiceMode_Prop2Conditions

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Proposition 2** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.17). If `V̄ : ℝ → ℝ` and an interval policy `π̄` satisfy the six
conditions of Proposition 2 (`Prop2Conditions`), then `V̄` is the value function `V*` and `π̄` is
an optimal policy: `V*(x) = V̄(x)` for every `x`, a `π̄`-feedback control system exists from every
`x`, and every `π̄`-feedback control system started at `x` attains `V*(x)`.

**Formalization Note.** `V̄ ≥ 0` (Condition 1), so `ENNReal.ofReal (V̄ x)` is `V̄(x)` itself. -/
theorem proposition_2 (p : Params) (V : ℝ → ℝ) (π : ℝ → Mode) (h : Prop2Conditions p V π) :
    (∀ x : ℝ, optimalCLV p x = ENNReal.ofReal (V x)) ∧
    (∀ x : ℝ, ∃ S : ControlSystem p x, S.IsFeedback π) ∧
    ∀ (x : ℝ) (S : ControlSystem p x), S.IsFeedback π → S.clv = optimalCLV p x := by sorry

end ChurnServiceMode
