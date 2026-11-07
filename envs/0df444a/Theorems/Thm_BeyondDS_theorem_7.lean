-- Prove2me | Theorems.Thm_BeyondDS_theorem_7
-- name    : BeyondDS.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:26.841758+00:00
-- url     : https://prove2.me/theorems/36aaf785-64cb-472a-bf11-77b6c7e160c4
-- title:
--   Theorem 7 — adaptive all-to-all dissemination in seven rounds with $O(n\sqrt{n\lambda})$ expected messages
-- statement:
--   There are absolute constants $c,C'>0$ such that the following holds for the protocol of §7.4 with parameters (19), every perfectly correct scheme, every $n=2t+1$ with $\lambda\ge1024\log(n+1)$, every input strings, and every prefix: an already corrupted set $C_0$ with $|C_0|\le t$, honestly generated keys, a log of earlier signatures containing no data of this instance, and any adversary and adversary state. Let $\epsilon_{sig}$ be the probability, in this execution, that an accepted acknowledgement attributed to a currently uncorrupted identity has signed data $(\mathrm{Ack},sid,P)$ that this identity never signed. Then:
--
--   1. the protocol ends after seven rounds, and every recipient uncorrupted through round 7 has an output;
--   2. $\Pr[\text{some required payload is not delivered}]\le e^{-c\lambda}+\epsilon_{sig}$;
--   3. $\mathbb E[M]\le C'\,n\sqrt{n\lambda}$;
--   4. in the sparse case $K<n$:
--   $$\Pr[\text{not delivered}\wedge\neg\epsilon_{sig}\text{-event}]\le n\delta_{fin},\quad \mathbb E[M]\le 6nK+2nB+2n^2\delta_{ep},\quad \Pr[M>6nK+2nB]\le2\delta_{ep},$$
--   and $M\le6nK+n^2$ on every history;
--   5. in the dense case $K\ge n$, required delivery holds on every outcome and $M\le n(n-1)$.
--
--   The message bounds hold without conditioning on authentication success. This is the building block of every call of the broadcast compiler.
--
--   **Formalization Note** Rounds are counted from $0$, so "through round 5" and "through round 7" are rounds $4$ and $6$. The protocol has no election, so the election law is unused.
--
--   Differences from the source:
--
--   - generalization: (21) Pr[not delivered] ≤ nδfin + ϵsig → the joint form Pr[not delivered ∧ no acknowledgement forgery] ≤ nδfin; reason: it implies (21), and it is the form the proof gives (p.28)
--   - reading: "after every fixed preceding execution history" → every start configuration with |C₀| ≤ t, keys from key generation, any adversary state, and an earlier signature log with no payload or acknowledgement of this instance; reason: "An instance identifier sid … is distinct from the identifiers of its other instances" (p.22)
--   - encoding: exp(−Ω(λ)) and O(n√(nλ)) → ∃ absolute constants c, C′ > 0 before all quantifiers; reason: the meaning of the asymptotic notation
--   - encoding: "never signed" → not in the signature log at the end of the execution; reason: same event
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model (decision 7)
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 7, p.27 (PDF p.28), eqs. (21)–(24); task and ϵsig, §7.1, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Theorem 7 (Adaptive all-to-all dissemination), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.27 (PDF 28), eqs. (21)–(24): with `λ ≥ 1024 log(n + 1)` and `K, B` of (19), the protocol of §7.4
terminates in seven rounds; all-to-all dissemination fails with probability at most `exp(−Ω(λ)) + ϵsig`, with `ϵsig` the probability of an acknowledgement forgery in this execution; its expected number
of messages sent before sender corruption is `O(n√(nλ))`. In the sparse case `K < n` the bounds (21)–(24) hold, and in the dense case `K ≥ n` delivery is deterministic and `M ≤ n(n − 1)`.

**Formalization Note.** Every clause holds from every prefix: any corrupted set `C₀` with `|C₀| ≤ t`, any honestly generated keys, any log of earlier signatures, any adversary and adversary state. (21) is
stated in the joint form the proof gives, `Pr[not delivered ∧ no acknowledgement forgery] ≤ nδfin`, which implies (21) and does not condition on authentication success (p.28). Rounds are counted from `0`, so the cutoffs "through round 5" and "through
round 7" are `4` and `6`. There is no election in this protocol, so `E` is unused.
The earlier log holds no payload or acknowledgement of instance `sid`: "An instance identifier sid is supplied to all players by the invoking protocol and
is distinct from the identifiers of its other instances" (p.22). -/
theorem theorem_7 :
    ∃ c C₀' : ℝ, 0 < c ∧ 0 < C₀' ∧
      ∀ (sid : ℕ) (x : (P : Params) → Fin P.n → Str) (S : Sig) (P : Params) (y : Bool)
        (E : List (Event P.n (Envelope Str) (ProgState (Envelope Str) (LS Str))) → PMF (Fin P.n))
        (A : Adversary P.n (Envelope Str) (ProgState (Envelope Str) (LS Str))) (a : A.σ)
        (pk sk : Fin P.n → Str) (C₀ : Finset (Fin P.n)) (signLog : List (Fin P.n × Str))
        (obs : List (Obs P.n (Envelope Str) (ProgState (Envelope Str) (LS Str)))),
        S.Correct → (∀ i, ∃ co, S.gen co = (pk i, sk i)) → C₀.card ≤ P.t →
        (∀ e ∈ signLog, (∀ (j : ℕ) (Q : Payload Str), e.2 ≠ encDatum id (Datum.ack sid j Q)) ∧
          ∀ (src : ℕ) (body : Str), e.2 ≠ encDatum id (Datum.payload sid src body)) →
        1024 * Real.log ((P.n : ℝ) + 1) ≤ P.lam →
        let D := execFrom (dissem sid x) S P E A (Config.start (dissem sid x) P y pk sk C₀ signLog a obs)
        (∀ ω ∈ D.support, ω.round = 7 ∧
          ∀ r, ω.UncorruptedThrough r 6 → ∃ rr o, recOf ω r sid = some rr ∧ rr.output = some o) ∧
        prob D {ω | NotDelivered sid ω} ≤
          ENNReal.ofReal (Real.exp (-(c * P.lam))) + prob D {ω | AckForge sid ω} ∧
        expect D msgCount ≤ ENNReal.ofReal (C₀' * (P.n * Real.sqrt ((P.n : ℝ) * P.lam))) ∧
        (paramK P < P.n →
          prob D {ω | NotDelivered sid ω ∧ ¬ AckForge sid ω} ≤
              ENNReal.ofReal (P.n * deltaFin P.n (paramK P)) ∧
          expect D msgCount ≤
              ENNReal.ofReal (6 * P.n * paramK P + 2 * P.n * paramB P + 2 * (P.n : ℝ) ^ 2 * deltaEp P.n (paramK P)) ∧
          prob D {ω | 6 * P.n * paramK P + 2 * P.n * paramB P < msgCount ω} ≤
              ENNReal.ofReal (2 * deltaEp P.n (paramK P)) ∧
          ∀ ω ∈ D.support, msgCount ω ≤ 6 * P.n * paramK P + P.n ^ 2) ∧
        (P.n ≤ paramK P →
          ∀ ω ∈ D.support, ¬ NotDelivered sid ω ∧ msgCount ω ≤ P.n * (P.n - 1)) := by sorry

end BeyondDS
