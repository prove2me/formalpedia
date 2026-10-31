-- Prove2me | Theorems.Thm_DworczakDACC_claim_3
-- name    : DworczakDACC.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:51.384667+00:00
-- url     : https://prove2.me/theorems/d24f7ae9-4152-49a4-8204-d47e2549cf85
-- title:
--   Claim 3 — the DACC algorithm stops in finite time (corrected: stack exit when no acceptable partner remains)
-- statement:
--   Let $\Phi$ name every agent infinitely often and fix any order of blocks (a)/(b). Then the run of DACC($\Phi$) reaches the stopping criterion at some finite time: there is a time at which every agent holds the best option of its budget set.
--
--   Differences from the source:
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; with the printed test the claim is false (the counterexample never stops)
--   - generalization: items (a) and (b) of "i applies" executed in some order (footnote a, p. 8: "in any order, even random") → the order is a parameter ord : ℕ → Bool (one choice per time step), universally quantified; reason: every resolution of footnote a, including a random one along each sample path, is some ord
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Claim 3, p. 9

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_IsAdmissible
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_run

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Claim 3: the DACC algorithm stops in finite time.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Claim 3,
p. 9: "The DACC algorithm stops in finite time."

For every `Φ` naming every agent infinitely often and every (a)/(b) order `ord`, there is a time
`t` at which the stopping criterion holds in `run Mk Φ ord t`.

**Formalization Note.** The run uses the corrected stack exit ("µ(i) ≠ ∅ or no acceptable
partner left in Bᵢ"); with the printed exit "Bᵢ = ∅" the claim is false (counterexample in the
mission description). -/
theorem claim_3 (Mk : Market D H) (Φ : ℕ → D ⊕ H) (hΦ : IsAdmissible Φ) (ord : ℕ → Bool) :
    ∃ t, Stopped Mk (run Mk Φ ord t) := by sorry

end DworczakDACC
