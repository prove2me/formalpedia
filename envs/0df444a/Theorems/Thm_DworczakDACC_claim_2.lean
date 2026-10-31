-- Prove2me | Theorems.Thm_DworczakDACC_claim_2
-- name    : DworczakDACC.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:56.305995+00:00
-- url     : https://prove2.me/theorems/caa5f2d2-4223-4331-8b42-652cf6db1f7d
-- title:
--   Claim 2 — every compensation chain stops in finite time (corrected: stack exit when no acceptable partner remains)
-- statement:
--   For every order $\Phi$, every order of blocks (a)/(b) and every time $t$ of the run of DACC($\Phi$), there is a later time $t'\ge t$ at which the stack $CC$ of agents to be compensated is empty, or the algorithm has stopped.
--
--   So the compensation chains started in a round all end, and the next round begins (or the algorithm has already stopped). This is what makes the end of every round well defined in the termination argument.
--
--   Differences from the source:
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; with the printed test the claim is false: in the counterexample the stack never empties and the algorithm never stops
--   - encoding: every CC (the chain (i₀, i₁, …) defined on p. 9) stops in finite time → from every time t the stack CC eventually empties or the run stops; reason: the CCs of a round ("zero, one, or two CCs", footnote 8) are exactly the contents of the stack of Algorithm 1; the loop guard is tested at every time step, so the run may stop with a non-empty stack
--   - generalization: Φ takes every value in N infinitely often (standing assumption, p. 6) → Φ : ℕ → D ⊕ H arbitrary; reason: while the stack is non-empty Φ is not consulted, and every finite prefix extends to an admissible order; the statement specializes to admissible Φ
--   - generalization: items (a) and (b) of "i applies" executed in some order (footnote a, p. 8: "in any order, even random") → the order is a parameter ord : ℕ → Bool (one choice per time step), universally quantified; reason: every resolution of footnote a, including a random one along each sample path, is some ord
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Claim 2, p. 9

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_run

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Claim 2: every compensation chain stops in finite time.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Claim 2,
p. 9: "Every CC stops in finite time."

For every order `Φ`, every (a)/(b) order `ord` and every time `t`, there is a time `t' ≥ t` at
which the stack `CC` is empty or the run has stopped.

**Formalization Note.** The compensation chains of a round (p. 9; "In every round, we can have
zero, one, or two CCs", footnote 8) are exactly the contents of the stack `CC` of Algorithm 1, so
"every CC stops" is "the stack empties", unless the stopping criterion holds first (the loop guard
is tested at every time step). `Φ` is arbitrary (a generalization: while the stack is non-empty
`Φ` is not consulted). The run uses the corrected stack exit ("µ(i) ≠ ∅ or no acceptable partner
left in Bᵢ"); with the printed exit "Bᵢ = ∅" the claim is false (counterexample in the mission
description). -/
theorem claim_2 (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) (t : ℕ) :
    ∃ t', t ≤ t' ∧ ((run Mk Φ ord t').stack = [] ∨ Stopped Mk (run Mk Φ ord t')) := by sorry

end DworczakDACC
