-- Prove2me | Theorems.Thm_CommitFrontRun_reveal_rule
-- name    : CommitFrontRun.reveal_rule
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:32.212607+00:00
-- url     : https://prove2.me/theorems/3d1be2be-df3e-45ca-88c1-0b5b217a63c1
-- title:
--   §3.1: $B$ fires iff $q\,\tilde P_B>f$ on path (corrected: indifference at $q\,\tilde P_B=f$)
-- statement:
--   Consider the commit-reveal game with the standing assumptions of §§2–3 and let $(A,B)$ be an equilibrium. Let $s$ be a state and $\sigma\in\Sigma$ a message such that the information set "state $s$, $A$ committed and revealed, $B$ committed the guess $\sigma$" has positive probability,
--   $$
--   p(s)\,\mathrm{commit}(s)\,\mathrm{reveal}(s)\,\mu(\mathrm{guess}\ \sigma)>0 .
--   $$
--   Then, after observing $A$'s reveal message $\sigma_A(s)$:
--
--   1. if $q\,\tilde P_B(\sigma,\sigma_A(s),s)>f$, $B$ fires with probability $1$;
--   2. if $q\,\tilde P_B(\sigma,\sigma_A(s),s)<f$, $B$ fires with probability $0$.
--
--   This is the reveal-stage rule of §3.1: firing costs $f$ and wins $\tilde P_B$ with probability $q$, so $B$ front-runs exactly when the expected gain exceeds the cost.
--
--   Differences from the source:
--
--   - correction: B will try to front run if and only if q · P̃_B(σ_B, σ**_A(s), s) > f → B fires with probability 1 if q · P̃_B > f and with probability 0 if q · P̃_B < f; at q · P̃_B = f firing is unconstrained; reason: at equality B is indifferent and may fire in equilibrium: S = {s1, s2}, Σ = {m1, m2}, σ_A(s_i) = m_i, p = (1/2, 1/2), c = 1, f = 2, q = 1/2, β = 1, P_A = (10, 10), P̃_B(m1, m1, s1) = 20, P̃_B(m1, m2, s2) = 4, all other P̃_B and off-argmax P̃_A equal to 0; the profile where A commits and reveals in both states and B commits m1 and fires at both m1 and m2 is an equilibrium (A gets 3 > 0 per state; B gets 3, the most any strategy yields), and B fires at m2 although q · P̃_B = f (checked in Lean)
--   - reading: B's information set after committing σ_B and observing A's reveal message → information sets of positive probability: p(s) · commit(s) · reveal(s) · μ(guess σ) > 0; reason: an ex-ante Nash equilibrium does not constrain B's firing at information sets of probability zero
--   - generalization: derived supposing there is no front running in equilibrium, so that A plays σ**_A → every equilibrium, whatever A's strategy; reason: B's firing decision at a reached information set does not depend on how A's strategy reached it; the source's case is included
--   - reading: equilibrium (footnote 16: Nash 1950) → Nash equilibrium of the ex-ante payoffs in behavior strategies (Model.IsEquilibrium); reason: footnote 16 cites Nash; the weakest standard notion, with no sequential rationality or beliefs added
--   - generalization: σ_A(s) is a bijection (p.10) → σ_A is injective (Model.σA_injective); reason: only injectivity is used (A's revealed message identifies the state); every bijection is injective, so the statement specializes to the source
--   - encoding: no state s with P_A(s) ∈ [c, c + c/β] (p.14) → ∀ s, P_A(s) < c ∨ c < β (P_A(s) − c) (Model.interval); reason: identical for β > 0; at β = 0 it reads c/0 = +∞, avoiding Lean's c / 0 = 0
--   - encoding: pure or mixed strategies of the commit-reveal game (pp.13–16) → behavior strategies: A's commit and reveal probabilities per state; B's lottery over none / clone / guess σ and firing probabilities per (guess, revealed message); payoffs ex ante, averaged over the prior; reason: Lean representation of the paper's finite game; mixed strategies appear on p.16
--   - encoding: off-path moves not spelled out → A not committing ends the game with payoffs (0, 0); a clone costs c and can never be revealed validly; if A does not reveal, B makes no further move; reason: Fig. 1 (p.11) gives (0, 0) for no message; a reveal from B's address fails the check S(addr, σ_A) (pp.13–14); without A's reveal there is nothing to front-run
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium

namespace CommitFrontRun

/-- **B's reveal-stage rule.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, p.15: "B's expected payoff from front-running is q · P̃_B(σ_B, σ**_A(s), s) − f.
Hence, B will try to front run if and only if q · P̃(σ_B, σ**_A(s), s) > f."

In every equilibrium (A, B), at every information set of B reached with positive probability
(state s, A commits and reveals, B committed the guess σ), B fires with probability 1 if
q · P̃_B(σ, σ_A(s), s) > f and with probability 0 if q · P̃_B(σ, σ_A(s), s) < f.

**Formalization Note** (correction) At q · P̃_B = f B is indifferent, and an equilibrium can have
him fire with probability 1 there (two states, p = (1/2, 1/2), c = 1, f = 2, q = 1/2, β = 1,
P_A = (10, 10), P̃_B(m1, m1, s1) = 20, P̃_B(m1, m2, s2) = 4), so the printed "if and only if" is
stated with both strict inequalities and the tie left free. Information sets of probability 0
are not constrained by an ex-ante Nash equilibrium. -/
theorem reveal_rule {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg)
    (A : StratA S) (B : StratB Msg) (hE : M.IsEquilibrium A B) (s : S) (σ : Msg)
    (hpath : 0 < M.p s * A.commit s * A.reveal s * B.μ (BCommit.guess σ)) :
    (M.f < M.q * M.PtB σ (M.σA s) s → B.fire σ (M.σA s) = 1) ∧
      (M.q * M.PtB σ (M.σA s) s < M.f → B.fire σ (M.σA s) = 0) := by sorry

end CommitFrontRun
