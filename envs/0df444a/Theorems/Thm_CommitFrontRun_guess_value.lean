-- Prove2me | Theorems.Thm_CommitFrontRun_guess_value
-- name    : CommitFrontRun.guess_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:06.009315+00:00
-- url     : https://prove2.me/theorems/e5c7c4d2-8396-4333-b8b6-b196bd5936b7
-- title:
--   §3.1: a committed guess is worth $\beta\pi-c$ to $B$
-- statement:
--   Consider the commit-reveal game with the standing assumptions of §§2–3. Suppose $A$ commits exactly in the states with $P_A(s)\ge c$ (i.e. $\sigma^{**}_A(s)\neq\emptyset$, eq. (3)) and reveals in each of them. Then:
--
--   1. the greatest ex-ante payoff $B$ can obtain while trying to front run, i.e. over his strategies that commit a guess with probability $1$ ($\mu(\mathrm{none})=\mu(\mathrm{clone})=0$), is
--   $$
--   \Pr\big(P_A(s)\ge c\big)\cdot(\beta\pi-c);
--   $$
--   2. the greatest ex-ante payoff $B$ can obtain over all his strategies is
--   $$
--   \Pr\big(P_A(s)\ge c\big)\cdot\max\{\beta\pi-c,\;0\}.
--   $$
--
--   Conditional on $A$ committing, a committed guess followed by optimal firing is worth $\beta\pi-c$ to $B$ (the paper: "if A sends a commit message and B tries to front run, B's expected payoff is $\beta\pi-c$"), and not committing is worth $0$. This is what makes $\beta\pi\le c$ the threshold of Proposition 2.
--
--   Differences from the source:
--
--   - reading: B's expected payoff βπ − c from a committed guess, conditional on A sending a commit message → (1) B's greatest ex-ante payoff over the strategies that commit a guess with probability 1 equals Pr(P_A(s) ≥ c) · (βπ − c), and (2) over all his strategies it equals Pr(P_A(s) ≥ c) · max{βπ − c, 0}, when A commits exactly where P_A(s) ≥ c and reveals there; reason: the conditional payoff is multiplied by the probability that A commits to make it ex ante; 'B tries to front run' is a committed guess (μ(none) = μ(clone) = 0) followed by optimal firing, with the best guess; (2) adds B's option not to commit
--   - encoding: π is a conditional expectation given σ**_A(s) ≠ ∅, undefined when that event has probability 0 → π = 0 when Pr(P_A(s) ≥ c) = 0; reason: Lean's division by 0; the event then never occurs
--   - generalization: σ_A(s) is a bijection (p.10) → σ_A is injective (Model.σA_injective); reason: only injectivity is used (A's revealed message identifies the state); every bijection is injective, so the statement specializes to the source
--   - encoding: no state s with P_A(s) ∈ [c, c + c/β] (p.14) → ∀ s, P_A(s) < c ∨ c < β (P_A(s) − c) (Model.interval); reason: identical for β > 0; at β = 0 it reads c/0 = +∞, avoiding Lean's c / 0 = 0
--   - encoding: pure or mixed strategies of the commit-reveal game (pp.13–16) → behavior strategies: A's commit and reveal probabilities per state; B's lottery over none / clone / guess σ and firing probabilities per (guess, revealed message); payoffs ex ante, averaged over the prior; reason: Lean representation of the paper's finite game; mixed strategies appear on p.16
--   - encoding: off-path moves not spelled out → A not committing ends the game with payoffs (0, 0); a clone costs c and can never be revealed validly; if A does not reveal, B makes no further move; reason: Fig. 1 (p.11) gives (0, 0) for no message; a reveal from B's address fails the check S(addr, σ_A) (pp.13–14); without A's reveal there is nothing to front-run
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_payoffB
import Definitions.Def_CommitFrontRun_Model_piValue

namespace CommitFrontRun

open Classical in
/-- **The value βπ − c of a committed guess.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, p.15: "His expected future payoff is, therefore: π ≡ max_{σ_B∈Σ} E_s[max{q ·
P̃_B(σ_B, σ**_A(s), s) − f, 0} | σ**_A(s) ≠ ∅] … Hence, if A sends a commit message and B tries to
front run, B's expected payoff is βπ − c."

If A commits exactly in the states with P_A(s) ≥ c (σ**_A(s) ≠ ∅, eq. (3)) and reveals in each of
them, then (1) the greatest ex-ante payoff B can obtain while trying to front run, i.e. over the
strategies that commit a guess with probability 1, is Pr(P_A(s) ≥ c) · (βπ − c); and (2) the
greatest ex-ante payoff B can obtain over all his strategies is Pr(P_A(s) ≥ c) · max{βπ − c, 0}.

**Formalization Note** The factor Pr(P_A(s) ≥ c) converts the paper's payoff conditional on A
committing into an ex-ante payoff; in (2) the max with 0 is B's option not to commit. -/
theorem guess_value {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg)
    (A : StratA S) (hcommit : ∀ s, A.commit s = if M.sends s then 1 else 0)
    (hreveal : ∀ s, M.sends s → A.reveal s = 1) :
    IsGreatest {v | ∃ B : StratB Msg, B.μ BCommit.none = 0 ∧ B.μ BCommit.clone = 0 ∧
        v = M.payoffB A B}
        ((∑ s, M.p s * (if M.sends s then (1 : ℝ) else 0)) * (M.β * M.piValue - M.c)) ∧
      IsGreatest {v | ∃ B : StratB Msg, v = M.payoffB A B}
        ((∑ s, M.p s * (if M.sends s then (1 : ℝ) else 0)) * max (M.β * M.piValue - M.c) 0) := by sorry

end CommitFrontRun
