-- Prove2me | Theorems.Thm_DworczakDACC_budget_invariant
-- name    : DworczakDACC.budget_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:54.073213+00:00
-- url     : https://prove2.me/theorems/67710865-aa45-42a7-9e7c-d981ec614c96
-- title:
--   §3, p. 9 — budget invariant: $i\in B_j$ or $j\in B_i$ at all times (corrected: stack exit when no acceptable partner remains)
-- statement:
--   Consider the run of DACC($\Phi$) for any order $\Phi$ and any order of blocks (a)/(b). At every time, for every man $d$ and every woman $h$:
--
--   1. $h\in B_d$ or $d\in B_h$;
--   2. if $d$ and $h$ are matched, then $h\in B_d$ and $d\in B_h$;
--   3. $\mu(d)=h$ if and only if $\mu(h)=d$.
--
--   The first clause is the invariant behind Claim 1: if $d\succ^h\mu(h)$ when the algorithm stops, then $d\notin B_h$, so $h\in B_d$, and condition (2.1) holds for all agents at termination. The second clause is the fact, used in the proof of Claim 1, that matched agents hold each other in their budget sets.
--
--   Differences from the source:
--   - generalization: Φ takes every value in N infinitely often (standing assumption, p. 6) → Φ : ℕ → D ⊕ H arbitrary; reason: the state at any time t depends on finitely many values of Φ, and every finite prefix extends to an order taking every value infinitely often; the statement specializes to admissible Φ
--   - generalization: items (a) and (b) of "i applies" executed in some order (footnote a, p. 8: "in any order, even random") → the order is a parameter ord : ℕ → Bool (one choice per time step), universally quantified; reason: every resolution of footnote a, including a random one along each sample path, is some ord
--   - generalization: i ∈ B_j or j ∈ B_i for all i ∈ N, j ∈ N_i, at all times → that invariant, together with "matched agents hold each other in their budget sets" (proof of Claim 1, p. 9) and µ(d) = h ↔ µ(h) = d; reason: a conjunction that contains the source's statement as its first clause; the third clause says that the two stored views of the matching are one matching
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; the printed algorithm's run agrees with the corrected run until a compensated agent is stuck, and then stays in that state forever, so its states are states of the corrected run and the invariant transfers to it
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), §3, p. 9 (unnumbered, after the proof of Claim 1); proof of Claim 1, p. 9

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_run

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Budget invariant: `i ∈ Bⱼ` or `j ∈ Bᵢ` at all times, and matched agents hold each other in
their budget sets.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), §3, p. 9
(unnumbered, after the proof of Claim 1): "A careful inspection shows that i ∈ Bj or j ∈ Bi, for
all i ∈ N, j ∈ Ni, at all times in DACC"; proof of Claim 1, p. 9: "whenever agents are matched,
they have each other in their respective budget sets".

For every order `Φ`, every resolution `ord` of the (a)/(b) order, every time `t`, every man `d`
and every woman `h`, in the state `run Mk Φ ord t`:
1. `h ∈ B_d` or `d ∈ B_h`;
2. if `d` and `h` are matched, then `h ∈ B_d` and `d ∈ B_h`;
3. the two stored views of the matching agree: `µ(d) = h` iff `µ(h) = d`.

**Formalization Note.** `Φ` need not name every agent infinitely often (a generalization: the
state at time `t` depends only on finitely many values of `Φ`, and every finite prefix extends to
an admissible order). Clause 3 is an encoding clause: the matching is stored from both sides.
The run is that of the algorithm with the corrected stack exit (`step`); the invariant does not
depend on the exit rule. -/
theorem budget_invariant (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) (t : ℕ) (d : D)
    (h : H) :
    (h ∈ (run Mk Φ ord t).budM d ∨ d ∈ (run Mk Φ ord t).budW h) ∧
      ((run Mk Φ ord t).mateM d = some h →
        h ∈ (run Mk Φ ord t).budM d ∧ d ∈ (run Mk Φ ord t).budW h) ∧
      ((run Mk Φ ord t).mateM d = some h ↔ (run Mk Φ ord t).mateW h = some d) := by sorry

end DworczakDACC
