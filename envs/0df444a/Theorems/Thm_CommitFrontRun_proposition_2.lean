-- Prove2me | Theorems.Thm_CommitFrontRun_proposition_2
-- name    : CommitFrontRun.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:29.596988+00:00
-- url     : https://prove2.me/theorems/df681906-7ca4-4f90-9553-5337d59f31b9
-- title:
--   Proposition 2: an equilibrium without front running exists iff $\beta\pi\le c$; otherwise every equilibrium carries a front-running threat (corrected: existential (ii), threat in (iii))
-- statement:
--   Consider the commit-reveal game with the standing assumptions of §§2–3 (finite non-empty $S$ and $\Sigma$, a prior $p$, $c>0$, $f>c$, $q\in[0,1]$, $\beta\in[0,1]$, $\sigma_A(s)$ the unique and injective maximizer of $\tilde P_A(\cdot,s)$, and no state with $P_A(s)\in[c,c+c/\beta]$). Let $\pi$ be the value of a blind guess (p.15). Then:
--
--   1. an equilibrium exists;
--   2. ("guessing is hard for $B$") if $\beta\pi\le c$, there is an equilibrium with no front running: its on-path probability of front running is $0$ and $B$'s front-running threat over the states with $P_A(s)\ge c$ is $0$; moreover it is the backward-induction equilibrium the paper describes: at every information set, reached or not, $B$ fires his committed guess $\sigma$ at $A$'s revealed $\sigma_A(s)$ when $q\,\tilde P_B(\sigma,\sigma_A(s),s)>f$ and not when $<f$, and $A$, having committed in state $s$, reveals when $(1-q\,\mathrm{threat}(\sigma_A(s)))\,P_A(s)>c$ and not when $<c$;
--   3. ("guessing is easy for $B$") if $\beta\pi>c$, every equilibrium has a strictly positive front-running threat: with positive probability over the states with $P_A(s)\ge c$, $B$ fires at $A$'s reveal message.
--
--   Together, 2 and 3 say that an equilibrium free of front running exists if and only if $\beta\pi\le c$. The threshold compares the cost $c$ of a commit message with the discounted value $\beta\pi$ of a guess committed before seeing $A$'s message.
--
--   Differences from the source:
--
--   - correction: if π ≤ c/β, there is no front-running in equilibrium (read: in every equilibrium) → if βπ ≤ c, there exists an equilibrium with zero on-path front running and zero threat, in which B's firing and A's reveal are moreover optimal at every information set, reached or not; reason: the universal reading is false: S = {s1, s2, s3}, p = (1/10, 8/10, 1/10), Σ = {m1, m2, m3}, σ_A(s_i) = m_i, c = 2, f = 3, q = 1/2, β = 1, P_A = (100, 6, 100), P̃_B(m1, ·, ·) = 26 at (m1, s1) and 31/5 at (m2, s2), all other P̃_B = 0; π = 27/25 ≤ 2, yet A committing and revealing in s1, s3 only and B committing m1 and firing at m1, m2 is an equilibrium with front running of probability 1/10 (checked in Lean); the paper's p.15 argument proves the existential form
--   - correction: if π > c/β, front running occurs with strictly positive probability in equilibrium → if βπ > c, every equilibrium has a strictly positive front-running threat ∑_s p(s) 1[P_A(s) ≥ c] threat(σ_A(s)); reason: on-path front running can be 0 in every equilibrium: one state and one message, c = 1, f = 2, q = 1/2, β = 1, P_A = 3, P̃_B = 10 give π = 3 > 1, but whenever A commits B's best reply is to guess and fire, leaving A with −1/2 < 0, so A never commits; the threat of B's equilibrium strategy is 1 (checked in Lean), the deterrence the paper describes on p.11
--   - reading: existence of an equilibrium (footnote 16) → clause 1, ∃ A B, IsEquilibrium A B; reason: footnote 16 asserts existence; it makes clause 3 non-vacuous
--   - reading: equilibrium (footnote 16: Nash 1950) → Nash equilibrium of the ex-ante payoffs in behavior strategies (Model.IsEquilibrium); reason: footnote 16 cites Nash; the weakest standard notion, with no sequential rationality or beliefs added, so the universal clause 3 is at its strongest; for the existential clause 2 the witness is additionally required to be sequentially rational in B's firing and A's reveal (the backward-induction equilibrium of p.15), so clause 2 is not weakened by the choice
--   - encoding: π ≤ c/β and π > c/β → β · π ≤ c and c < β · π; reason: identical for β > 0; β = 0 is allowed and makes c/β = +∞
--   - encoding: π is a conditional expectation given σ**_A(s) ≠ ∅, undefined when that event has probability 0 → π = 0 when Pr(P_A(s) ≥ c) = 0; reason: Lean's division by 0; the event then never occurs
--   - generalization: σ_A(s) is a bijection (p.10) → σ_A is injective (Model.σA_injective); reason: only injectivity is used (A's revealed message identifies the state); every bijection is injective, so the statement specializes to the source
--   - encoding: no state s with P_A(s) ∈ [c, c + c/β] (p.14) → ∀ s, P_A(s) < c ∨ c < β (P_A(s) − c) (Model.interval); reason: identical for β > 0; at β = 0 it reads c/0 = +∞, avoiding Lean's c / 0 = 0
--   - encoding: pure or mixed strategies of the commit-reveal game (pp.13–16) → behavior strategies: A's commit and reveal probabilities per state; B's lottery over none / clone / guess σ and firing probabilities per (guess, revealed message); payoffs ex ante, averaged over the prior; reason: Lean representation of the paper's finite game; mixed strategies appear on p.16
--   - encoding: off-path moves not spelled out → A not committing ends the game with payoffs (0, 0); a clone costs c and can never be revealed validly; if A does not reveal, B makes no further move; reason: Fig. 1 (p.11) gives (0, 0) for no message; a reveal from B's address fails the check S(addr, σ_A) (pp.13–14); without A's reveal there is nothing to front-run
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, Proposition 2, p.16; footnote 16, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium
import Definitions.Def_CommitFrontRun_Model_piValue
import Definitions.Def_CommitFrontRun_Model_threatTotal
import Definitions.Def_CommitFrontRun_Model_frontRunOnPath

namespace CommitFrontRun

/-- **Proposition 2 (corrected).**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, Proposition 2, p.16: "If π ≤ c/β (i.e., 'guessing is hard for B'), then there is
no front-running in equilibrium. If instead π > c/β (i.e., 'guessing is easy for B'), front
running occurs with strictly positive probability in equilibrium." Existence: footnote 16, p.15.

1. An equilibrium exists.
2. If βπ ≤ c, there is an equilibrium with zero on-path front running and zero front-running
   threat, which is moreover the backward-induction one: B fires (or not) optimally at every
   information set "guess σ, A revealed σ_A(s)", and A reveals (or not) optimally in every state
   after committing, whether or not these information sets are reached.
3. If βπ > c, every equilibrium has a strictly positive front-running threat: B fires at A's
   reveal message with positive probability over the states with P_A(s) ≥ c.

**Formalization Note**
* Clause 2 is existential: read as "every equilibrium has no front running" it is false
  (3 states, p = (1/10, 8/10, 1/10), π = 27/25 ≤ c/β = 2, an equilibrium with front running of
  probability 1/10). The paper's p.15 argument proves the existential form.
* Clause 3 measures the threat, not on-path front running: with one state, c = 1, f = 2,
  q = 1/2, β = 1, P_A = 3, P̃_B = 10 one has π = 3 > c/β but A never commits in any equilibrium,
  so on-path front running is 0 in every equilibrium while the threat is 1.
* π ≤ c/β is written βπ ≤ c (β = 0 is allowed); π = 0 when Pr(P_A(s) ≥ c) = 0. -/
theorem proposition_2 {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg) :
    (∃ (A : StratA S) (B : StratB Msg), M.IsEquilibrium A B) ∧
      (M.β * M.piValue ≤ M.c →
        ∃ (A : StratA S) (B : StratB Msg), M.IsEquilibrium A B ∧
          M.frontRunOnPath A B = 0 ∧ M.threatTotal B = 0 ∧
          (∀ s σ, (M.f < M.q * M.PtB σ (M.σA s) s → B.fire σ (M.σA s) = 1) ∧
            (M.q * M.PtB σ (M.σA s) s < M.f → B.fire σ (M.σA s) = 0)) ∧
          (∀ s, (M.c < (1 - M.q * B.threat (M.σA s)) * M.PA s → A.reveal s = 1) ∧
            ((1 - M.q * B.threat (M.σA s)) * M.PA s < M.c → A.reveal s = 0))) ∧
      (M.c < M.β * M.piValue →
        ∀ (A : StratA S) (B : StratB Msg), M.IsEquilibrium A B → 0 < M.threatTotal B) := by sorry

end CommitFrontRun
