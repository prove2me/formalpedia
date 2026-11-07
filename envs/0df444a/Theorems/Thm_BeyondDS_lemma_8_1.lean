-- Prove2me | Theorems.Thm_BeyondDS_lemma_8_1
-- name    : BeyondDS.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:15:11.638284+00:00
-- url     : https://prove2.me/theorems/5dd6f57d-6658-4efc-b102-cd3de542764a
-- title:
--   Lemma 8.1 — terminal dissemination and cost, (27)
-- statement:
--   For the compiler with $\lambda\ge1024\log(n+1)$, a perfectly correct scheme, any election law and any adversary:
--
--   1. at every prefix before $g$ (and before the public final deadline) every uncorrupted player is active;
--   2. ($c_A$) from every prefix at the start of a call before $g$ with no earlier forgery or statistical delivery failure, the expected number of messages of that call is at most $c_A$;
--   3. ($c_T$) from every successful stopping prefix at $g$ (no forgery, no statistical delivery failure in a call before $g$, and every uncorrupted player holding a termination certificate at the boundary of $g$), the expected number of later messages is at most $c_T$;
--   4. from every prefix at the start of a call before $g$, the probability that some terminal source's delivery fails in that call while its possession invariant holds is at most $n\delta_{fin}$;
--   5. if $g<\infty$ and no forgery or statistical delivery failure occurred through $g$, every player uncorrupted at $g$ holds a termination certificate at that boundary, and no honest message is sent after one further call and two further rounds.
--
--   Here $c_A=6nK+2nB+2n^2\delta_{ep}$ and $c_T=8nK+nB+n^2\delta_{ep}$ in the sparse case and $n(n-1)$, $2n(n-1)$ in the dense case.
--
--   **Formalization Note** New messages are $M(\omega)-M(\text{prefix})$, a difference of a count that only grows. Call $g$ ends at round $7g+6$ counted from $0$; one further call and two rounds end at round $7g+15$.
--
--   Differences from the source:
--
--   - reading: "cA, a uniform conditional expected message bound per call before g", "cT, the expected traffic strictly after g" → expectation bounds from every reachable prefix at a call start before g without earlier failure, and from every successful stopping prefix at g; reason: the definitions of p.31, with conditioning on a prefix as the law of the continuation from that configuration
--   - reading: "any such successful stopping prefix at g", a history with "no such delivery or authentication failure through g" at which "every player uncorrupted at g has a termination certificate" → a prefix at the boundary of call g with no forgery, no statistical delivery failure in any call before g, and a verifying termination certificate in the evidence each uncorrupted player has received; reason: the outputs of call g are processed only after that boundary, so its delivery is stated by its consequence on p.31, the held certificates
--   - reading: "Before g or the public final deadline … no honest player has halted" → at every prefix of at most the round cap with no qualifying call completed, every uncorrupted player is active; reason: g is the first qualifying call completion
--   - reading: "all honest-sent traffic ends within one further call and two further rounds" → no honest transmission after the boundary of round 7g + 15; reason: rounds are counted from 0
--   - encoding: the dense case "one may take cA = n(n − 1) and cT = 2n(n − 1)" → the definitions of cA, cT branch on K < n; reason: same values
--   - generalization: the late common election oracle of §§4.3, 5.1 (uniform, or within ζ of uniform, given the transcript) → any election law, a function of the transcript at the reveal boundary; reason: the conclusion holds whatever identity is elected, and the oracle is one such law
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model (decision 7)
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 8.1, p.31 (PDF p.32), eq. (27); g, cA, cT, §8.3, p.31

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Lemma 8.1 (Terminal dissemination and cost), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.31 (PDF 32), eq. (27): before `g` or the public final deadline, whichever occurs first, no honest player has halted. In the sparse case, before any earlier delivery or authentication failure, `cA ≤ 6nK + 2nB + 2n²δep`,
`cT ≤ 8nK + nB + n²δep`. For each call reached before `g`, conditional on its starting prefix, the probability that a terminal source's required delivery fails while its acknowledgement-possession invariant holds at recovery is at most `nδfin`, jointly over all terminal sources in that call. If `g < ∞`, then on histories with no
such delivery or authentication failure through `g`, every player uncorrupted at `g` has a termination certificate at that boundary. Thereafter all honest-sent traffic ends within one further call and two further rounds. The tail bound in (27) is conditional on any such successful stopping prefix at `g`. In the dense case one
may take `cA = n(n − 1)` and `cT = 2n(n − 1)`.

**Formalization Note.** `cA` and `cT` are the values in `BeyondDS.cA`, `BeyondDS.cT` and they bound expected new messages from every reachable prefix: a point of `prefixLaw` at round `7c` before `g` with no earlier failure, or a `SuccessfulStop` prefix at `g`. New messages are counted by `msgCount ω − msgCount cf`, a truncated difference of a log that only grows.
Call `g` ends at round `7g + 6` counted from `0`, and two rounds after one further call end at round `7g + 15`. "No authentication failure through
`g`" is `¬ ForgeBefore (7g + 7)`: no forgery before the outputs of call `g` have been processed. -/
theorem lemma_8_1 (J : Params → ℕ) (S : Sig) (hS : S.Correct) (P : Params) (x : Bool)
    (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (A : Adversary P.n CMsg CSt)
    (hlam : 1024 * Real.log ((P.n : ℝ) + 1) ≤ P.lam) :
    (∀ R, R ≤ (compiler J).roundCap P → ∀ cf ∈ (prefixLaw (compiler J) S P x E A R).support, gCall cf = none →
      ∀ i, i ∉ cf.corrupted → cf.active i = true) ∧
    (∀ c, c < 6 * J P + 4 → ∀ cf ∈ (prefixLaw (compiler J) S P x E A (7 * c)).support, gCall cf = none → ¬ Forge cf →
      (∀ c', c' < c → ¬ DeliveryFail P (J P) c' cf) →
      expect (runRounds (compiler J) S P E A 7 cf) (fun ω => msgCount ω - msgCount cf) ≤ ENNReal.ofReal (cA P)) ∧
    (∀ g, ∀ cf ∈ (prefixLaw (compiler J) S P x E A (7 * (g + 1))).support, SuccessfulStop S P (J P) g cf →
      expect (execFrom (compiler J) S P E A cf) (fun ω => msgCount ω - msgCount cf) ≤ ENNReal.ofReal (cT P)) ∧
    (∀ c, c < 6 * J P + 4 → ∀ cf ∈ (prefixLaw (compiler J) S P x E A (7 * c)).support, gCall cf = none →
      prob (runRounds (compiler J) S P E A 7 cf) {ω | TerminalFail P (J P) c ω} ≤
        ENNReal.ofReal (P.n * deltaFin P.n (paramK P))) ∧
    (∀ ω ∈ (exec (compiler J) S P x E A).support, ∀ g, gCall ω = some g → ¬ ForgeBefore (7 * g + 7) ω →
      (∀ c, c ≤ g → ¬ DeliveryFail P (J P) c ω) →
      (∀ i, ω.UncorruptedThrough i (7 * g + 6) → ∀ rr o, recOf ω i g = some rr → rr.output = some o →
        ∃ b, o.HoldsTerm (publicCtx P (J P) ω) b) ∧
      NoSendAfter (7 * g + 15) ω) := by sorry

end BeyondDS
