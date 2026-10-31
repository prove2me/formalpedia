-- Prove2me | Theorems.Thm_CommitFrontRun_equilibrium_exists
-- name    : CommitFrontRun.equilibrium_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:09.985459+00:00
-- url     : https://prove2.me/theorems/e11a6a51-d467-4c9a-a4d4-3320357dc0e5
-- title:
--   Footnote 16: the commit-reveal game has an equilibrium
-- statement:
--   Every commit-reveal game satisfying the standing assumptions of §§2–3 has an equilibrium: there are strategies $A$ and $B$ such that neither player gains by a unilateral deviation.
--
--   The paper notes that existence follows from the finiteness of the players' strategy spaces, as in Nash (1950). It is clause (i) of Proposition 2 and is what makes the universal clause (iii) non-vacuous.
--
--   Differences from the source:
--
--   - reading: equilibrium (footnote 16: Nash 1950) → Nash equilibrium of the ex-ante payoffs in behavior strategies (Model.IsEquilibrium); reason: footnote 16 cites Nash; the weakest standard notion, with no sequential rationality or beliefs added
--   - generalization: σ_A(s) is a bijection (p.10) → σ_A is injective (Model.σA_injective); reason: only injectivity is used (A's revealed message identifies the state); every bijection is injective, so the statement specializes to the source
--   - encoding: no state s with P_A(s) ∈ [c, c + c/β] (p.14) → ∀ s, P_A(s) < c ∨ c < β (P_A(s) − c) (Model.interval); reason: identical for β > 0; at β = 0 it reads c/0 = +∞, avoiding Lean's c / 0 = 0
--   - encoding: pure or mixed strategies of the commit-reveal game (pp.13–16) → behavior strategies: A's commit and reveal probabilities per state; B's lottery over none / clone / guess σ and firing probabilities per (guess, revealed message); payoffs ex ante, averaged over the prior; reason: Lean representation of the paper's finite game; mixed strategies appear on p.16
--   - encoding: off-path moves not spelled out → A not committing ends the game with payoffs (0, 0); a clone costs c and can never be revealed validly; if A does not reveal, B makes no further move; reason: Fig. 1 (p.11) gives (0, 0) for no message; a reveal from B's address fails the check S(addr, σ_A) (pp.13–14); without A's reveal there is nothing to front-run
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, footnote 16, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium

namespace CommitFrontRun

/-- **Existence of equilibrium.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, footnote 16, p.15: "The existence of the equilibrium follows from the fact that the
players' strategy space is finite, as noted already in Nash (1950)."

Every commit-reveal game has an equilibrium (a Nash equilibrium in behavior strategies). -/
theorem equilibrium_exists {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg) :
    ∃ (A : StratA S) (B : StratB Msg), M.IsEquilibrium A B := by sorry

end CommitFrontRun
