-- Prove2me | Theorems.Thm_DworczakDACC_claim_4
-- name    : DworczakDACC.claim_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:07.575618+00:00
-- url     : https://prove2.me/theorems/cd92f6fb-f2da-41f9-8419-858d0a3cd78f
-- title:
--   Claim 4 — every stable matching is a DACC outcome, without compensation chains (corrected: stack exit when no acceptable partner remains)
-- statement:
--   Let the market be one-to-one with at least one agent, and let $\mu$ be a stable matching. Then there is an order $\Phi$ naming every agent infinitely often such that, for every order of blocks (a)/(b),
--
--   1. DACC($\Phi$) stops in finite time with outcome $\mu$, and
--   2. no compensation chain ever starts: the stack $CC$ is empty at every time.
--
--   This is the converse half of Theorem 1: every stable matching is reached by some DACC algorithm, and it can be reached without compensation chains.
--
--   Differences from the source:
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; in a run whose stack is always empty the exit test is never evaluated, so for the order Φ the claim provides, the run is the same under the printed and the corrected test
--   - encoding: men M, women W, strict preferences ≻ⁱ on Nᵢ ∪ {∅}, matching and stability as on p. 5 → RuralHospitals.Market D H with capacity h = 1 for all h (men = D, women = H, injective ranks with smaller = better, none = ∅); Market.IsStable; reason: with capacity 1, IsStable is exactly p. 5's stability (one-to-one, acceptable partners, j ≻ⁱ µ(i) ⇒ µ(j) ≻ʲ i); same instances
--   - encoding: any finite market → [Nonempty (D ⊕ H)]; reason: if N = ∅ there is no sequence Φ : ℕ → N, so DACC(Φ) is undefined; the hypothesis excludes only that case
--   - generalization: an ordering Φ such that µ is the outcome of DACC(Φ) (one algorithm) → one Φ that works for every (a)/(b) order ord; reason: a single Φ for all orders implies the source's statement for any fixed resolution of footnote a
--   - encoding: Φ "does not lead to any compensation chains" → the stack is empty at every time; reason: a CC starts exactly when an agent is pushed on the stack
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Claim 4, p. 11

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_IsAdmissible
import Definitions.Def_DworczakDACC_run
import Definitions.Def_DworczakDACC_IsOutcome

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Claim 4: every stable matching is the outcome of some DACC(Φ), with no compensation
chains.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Claim 4,
p. 11: "For any stable µ, there is an ordering Φ such that µ is the outcome of DACC(Φ). Moreover,
µ can be achieved with an order Φ that does not lead to any compensation chains."

In a one-to-one market (every capacity `1`) with at least one agent, for every stable matching
`μ` there is an order `Φ` naming every agent infinitely often such that, for every (a)/(b) order
`ord`, DACC(Φ) stops with outcome `μ` and the stack `CC` is empty at every time.

**Formalization Note.** `Nonempty (D ⊕ H)`: with no agent there is no sequence `Φ : ℕ → N`, so
"DACC(Φ)" is undefined; the hypothesis excludes only that case. One `Φ` serves every (a)/(b)
order (a generalization of the paper's fixed algorithm). "Does not lead to any compensation
chains" is "the stack is empty at every time". The run uses the corrected stack exit. -/
theorem claim_4 (Mk : Market D H) (hcap : ∀ h, Mk.capacity h = 1) [Nonempty (D ⊕ H)]
    (μ : Assignment D H) (hμ : Mk.IsStable μ) :
    ∃ Φ : ℕ → D ⊕ H, IsAdmissible Φ ∧
      ∀ ord : ℕ → Bool, IsOutcome Mk Φ ord μ ∧ ∀ t, (run Mk Φ ord t).stack = [] := by sorry

end DworczakDACC
