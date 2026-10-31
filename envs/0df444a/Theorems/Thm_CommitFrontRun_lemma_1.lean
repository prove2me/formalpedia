-- Prove2me | Theorems.Thm_CommitFrontRun_lemma_1
-- name    : CommitFrontRun.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:16.291902+00:00
-- url     : https://prove2.me/theorems/35470d80-e6ad-46a0-b5e1-b4b80de6a0d3
-- title:
--   Lemma 1: no cloning, and no commit without reveal, in equilibrium
-- statement:
--   Consider the commit-reveal game with the standing assumptions of §§2–3 and let $(A,B)$ be an equilibrium. Then:
--
--   1. the probability that $A$ commits and $B$ clones her commit message is zero,
--   $$
--   \Big(\sum_{s}p(s)\,\mathrm{commit}(s)\Big)\,\mu(\mathrm{clone})=0;
--   $$
--   2. in every state $s$, the probability that $A$ commits but does not reveal is zero,
--   $$
--   p(s)\,\mathrm{commit}(s)\,(1-\mathrm{reveal}(s))=0 .
--   $$
--
--   This is the paper's Lemma 1: a clone costs $B$ a message and can never be revealed validly, and committing without revealing costs $A$ a message for nothing. It reduces $B$'s options in equilibrium to not committing or committing a guess.
--
--   Differences from the source:
--
--   - reading: there is no equilibrium in which σ_{B,1} = σ_{A,1}, or in which A commits but does not reveal → in every equilibrium these events have probability zero (weighted by the prior and by A's commit probability); reason: an ex-ante Nash equilibrium leaves choices at probability-zero information sets free (e.g. B's plan when A never commits, A's play in a state of prior 0), so the statement is about what happens with positive probability
--   - reading: equilibrium (footnote 16: Nash 1950) → Nash equilibrium of the ex-ante payoffs in behavior strategies (Model.IsEquilibrium); reason: footnote 16 cites Nash; the weakest standard notion, with no sequential rationality or beliefs added
--   - generalization: σ_A(s) is a bijection (p.10) → σ_A is injective (Model.σA_injective); reason: only injectivity is used (A's revealed message identifies the state); every bijection is injective, so the statement specializes to the source
--   - encoding: no state s with P_A(s) ∈ [c, c + c/β] (p.14) → ∀ s, P_A(s) < c ∨ c < β (P_A(s) − c) (Model.interval); reason: identical for β > 0; at β = 0 it reads c/0 = +∞, avoiding Lean's c / 0 = 0
--   - encoding: pure or mixed strategies of the commit-reveal game (pp.13–16) → behavior strategies: A's commit and reveal probabilities per state; B's lottery over none / clone / guess σ and firing probabilities per (guess, revealed message); payoffs ex ante, averaged over the prior; reason: Lean representation of the paper's finite game; mixed strategies appear on p.16
--   - encoding: off-path moves not spelled out → A not committing ends the game with payoffs (0, 0); a clone costs c and can never be revealed validly; if A does not reveal, B makes no further move; reason: Fig. 1 (p.11) gives (0, 0) for no message; a reveal from B's address fails the check S(addr, σ_A) (pp.13–14); without A's reveal there is nothing to front-run
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, Lemma 1, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium

namespace CommitFrontRun

/-- **Lemma 1 (No cloning in equilibrium).**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, Lemma 1, p.15: "There is no equilibrium in which σ_{B,1} = σ_{A,1}. There is also
no equilibrium in which A sends the commit message but not the reveal message."

In every equilibrium (A, B): the probability that A commits and B clones her commit message is
0, and in every state the probability that A commits but does not reveal is 0.

**Formalization Note** Equilibrium is ex-ante Nash, which does not constrain A in states of
prior probability 0, so both clauses are stated as prior-weighted (on-path) probabilities. -/
theorem lemma_1 {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg)
    (A : StratA S) (B : StratB Msg) (hE : M.IsEquilibrium A B) :
    (∑ s, M.p s * A.commit s) * B.μ BCommit.clone = 0 ∧
      ∀ s, M.p s * A.commit s * (1 - A.reveal s) = 0 := by sorry

end CommitFrontRun
