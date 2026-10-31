-- Prove2me | Theorems.Thm_CommitFrontRun_unthreatened_reply
-- name    : CommitFrontRun.unthreatened_reply
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:55.124439+00:00
-- url     : https://prove2.me/theorems/5fb930e2-9ce0-4ebd-a72a-85c9adb41836
-- title:
--   §3.1: when not threatened, $A$ plays $\sigma^{**}_A$ in equilibrium
-- statement:
--   Consider the commit-reveal game with the standing assumptions of §§2–3, including the interval assumption $P_A(s)\notin[c,c+c/\beta]$. Let $(A,B)$ be an equilibrium and $s$ a state with $p(s)>0$ at which $B$ never front-runs $A$'s message, $\mathrm{threat}(\sigma_A(s))=0$. Then
--
--   1. if $P_A(s)\ge c$, $A$ commits and reveals with probability $1$;
--   2. if $P_A(s)<c$, $A$ does not commit.
--
--   So without front running, $A$'s optimal message in the protocol is again $\sigma^{**}_A(s)$ of eq. (3): the protocol does not change the states in which $A$ wants to send her message.
--
--   Differences from the source:
--
--   - reading: suppose there is no front running in equilibrium so that A's optimal message is again σ**_A(s) → for every state s with p(s) > 0 at which B's threat at σ_A(s) is 0, A commits and reveals with probability 1 if P_A(s) ≥ c and does not commit if P_A(s) < c; reason: 'no front running' is B's zero threat at A's message; 'A's optimal message is σ**_A(s)' is A's strategy; states of prior 0 are excluded because ex-ante Nash does not constrain A there
--   - generalization: an equilibrium without front running → every equilibrium, at each state where the threat is 0; reason: the conclusion is local to the state; an equilibrium without front running has zero threat at every state A sends in
--   - reading: equilibrium (footnote 16: Nash 1950) → Nash equilibrium of the ex-ante payoffs in behavior strategies (Model.IsEquilibrium); reason: footnote 16 cites Nash; the weakest standard notion, with no sequential rationality or beliefs added
--   - generalization: σ_A(s) is a bijection (p.10) → σ_A is injective (Model.σA_injective); reason: only injectivity is used (A's revealed message identifies the state); every bijection is injective, so the statement specializes to the source
--   - encoding: no state s with P_A(s) ∈ [c, c + c/β] (p.14) → ∀ s, P_A(s) < c ∨ c < β (P_A(s) − c) (Model.interval); reason: identical for β > 0; at β = 0 it reads c/0 = +∞, avoiding Lean's c / 0 = 0
--   - encoding: pure or mixed strategies of the commit-reveal game (pp.13–16) → behavior strategies: A's commit and reveal probabilities per state; B's lottery over none / clone / guess σ and firing probabilities per (guess, revealed message); payoffs ex ante, averaged over the prior; reason: Lean representation of the paper's finite game; mixed strategies appear on p.16
--   - encoding: off-path moves not spelled out → A not committing ends the game with payoffs (0, 0); a clone costs c and can never be revealed validly; if A does not reveal, B makes no further move; reason: Fig. 1 (p.11) gives (0, 0) for no message; a reveal from B's address fails the check S(addr, σ_A) (pp.13–14); without A's reveal there is nothing to front-run
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, p.15; §3, p.14

import Mathlib
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium
import Definitions.Def_CommitFrontRun_Model_sends

namespace CommitFrontRun

/-- **A's equilibrium reply when she is not threatened is σ**_A.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, p.15: "suppose there is no front running in equilibrium so that A's optimal message
is again σ**_A(s) (see Equation 3)", with the interval assumption of p.14 ("if A expects no
front running, then the introduction of the protocol does not change the states of the world
for which A wants to send a message").

In every equilibrium (A, B), for every state s of positive prior probability at which B never
front-runs A's message: if P_A(s) ≥ c then A commits and reveals with probability 1, and if
P_A(s) < c then A does not commit. -/
theorem unthreatened_reply {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg)
    (A : StratA S) (B : StratB Msg) (hE : M.IsEquilibrium A B) (s : S) (hp : 0 < M.p s)
    (hthreat : B.threat (M.σA s) = 0) :
    (M.sends s → A.commit s = 1 ∧ A.reveal s = 1) ∧ (¬ M.sends s → A.commit s = 0) := by sorry

end CommitFrontRun
