-- Prove2me | Theorems.Thm_CommitFrontRun_unthreatened_value
-- name    : CommitFrontRun.unthreatened_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:52.130986+00:00
-- url     : https://prove2.me/theorems/7fce7179-f9db-4154-8a9c-f73becf8c967
-- title:
--   §3.1: $A$'s best payoff when unthreatened is $\max\{-c+\beta(P_A(s)-c),0\}$
-- statement:
--   Consider the commit-reveal game with the standing assumptions of §§2–3. Let $B$ be any strategy of $B$ and $s$ a state at which $B$ never front-runs $A$'s message, $\mathrm{threat}(\sigma_A(s))=0$. Then the greatest payoff $A$ can obtain in state $s$, over her commit and reveal probabilities $x,y\in[0,1]$, is
--   $$
--   \max\{-c+\beta(P_A(s)-c),\;0\}.
--   $$
--   Moreover, in every equilibrium $(A,B)$ with this $B$, if $p(s)>0$ then $A$'s equilibrium payoff in state $s$ is exactly this value.
--
--   The two terms are the payoff of committing and revealing (two messages, the prize one block late) and of staying out. The paper states this as $A$'s equilibrium payoff in the case "guessing is hard for $B$", where $B$ does not front-run.
--
--   Differences from the source:
--
--   - generalization: A's equilibrium payoff in the 'guessing is hard for B' case → A's greatest state-s payoff against every strategy of B whose threat at σ_A(s) is 0, and A's state-s payoff in every equilibrium whose B has threat 0 at σ_A(s), for p(s) > 0; reason: in the source's case B does not front-run (by Proposition 2 (ii) such an equilibrium exists when βπ ≤ c), so the source's claim is an instance; the hypothesis βπ ≤ c is replaced by the zero threat it is used for; states of prior 0 are excluded because ex-ante Nash does not constrain A there
--   - generalization: σ_A(s) is a bijection (p.10) → σ_A is injective (Model.σA_injective); reason: only injectivity is used (A's revealed message identifies the state); every bijection is injective, so the statement specializes to the source
--   - encoding: no state s with P_A(s) ∈ [c, c + c/β] (p.14) → ∀ s, P_A(s) < c ∨ c < β (P_A(s) − c) (Model.interval); reason: identical for β > 0; at β = 0 it reads c/0 = +∞, avoiding Lean's c / 0 = 0
--   - encoding: pure or mixed strategies of the commit-reveal game (pp.13–16) → behavior strategies: A's commit and reveal probabilities per state; B's lottery over none / clone / guess σ and firing probabilities per (guess, revealed message); payoffs ex ante, averaged over the prior; reason: Lean representation of the paper's finite game; mixed strategies appear on p.16
--   - encoding: off-path moves not spelled out → A not committing ends the game with payoffs (0, 0); a clone costs c and can never be revealed validly; if A does not reveal, B makes no further move; reason: Fig. 1 (p.11) gives (0, 0) for no message; a reveal from B's address fails the check S(addr, σ_A) (pp.13–14); without A's reveal there is nothing to front-run
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, p.16

import Mathlib
import Definitions.Def_CommitFrontRun_Model_stateValueA
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium

namespace CommitFrontRun

/-- **A's best payoff when she is not threatened.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, p.16: "It is easy to check that in the 'guessing is hard for B' case, A's
equilibrium payoff is max{−c + β(P_A(s) − c), 0}".

For every strategy B of B and every state s at which B never front-runs A's message
(`B.threat (σ_A(s)) = 0`), the greatest payoff A can obtain in state s over her commit and
reveal probabilities x, y ∈ [0, 1] is max{−c + β(P_A(s) − c), 0}; and in every equilibrium
(A, B) with this B, A's equilibrium payoff in s (if p(s) > 0) is exactly that value. -/
theorem unthreatened_value {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg)
    (B : StratB Msg) (s : S) (hthreat : B.threat (M.σA s) = 0) :
    IsGreatest {v | ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, v = M.stateValueA B s x y}
        (max (-M.c + M.β * (M.PA s - M.c)) 0) ∧
      ∀ A : StratA S, M.IsEquilibrium A B → 0 < M.p s →
        M.stateValueA B s (A.commit s) (A.reveal s) =
          max (-M.c + M.β * (M.PA s - M.c)) 0 := by sorry

end CommitFrontRun
