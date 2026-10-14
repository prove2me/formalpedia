-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Baseline_proposition_1
-- name    : AcquihiringMonopsony.Baseline.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:43.961122+00:00
-- url     : https://prove2.me/theorems/300e7207-67fd-4806-8431-5c0d618ccce1
-- title:
--   Proposition 1 — the acquirer hires iff v_a > v_s, then only through acquihiring; the employee prefers direct hiring
-- statement:
--   Consider the baseline model: a startup and an acquirer value an essential employee at $v_s$ and $v_a$, the employee enjoys a private benefit $b$ at the startup, wages are at least $\underline{w}$, and
--   $$
--   b > 0, \qquad \min\{v_a, v_s\} > b + \underline{w}.
--   $$
--   The acquirer first chooses between **direct hiring** (simultaneous wage competition with the startup) and **acquihiring** (a take-it-or-leave-it bid for the startup, followed by a wage offer from whichever firm then employs the worker). Fix any continuation equilibrium in undominated strategies of each subgame.
--   1. If $v_a > v_s$, the acquirer hires the employee, and does so through acquihiring: its bid is accepted, and its acquihiring payoff is strictly larger than its direct-hiring payoff.
--   2. If $v_a < v_s$, the acquirer does not hire the employee under either mode.
--   3. For all parameter values, the employee's payoff is strictly larger under direct hiring than under acquihiring.
--   4. Continuation equilibria of the direct-hiring subgame exist whenever $v_a \ne v_s + b$, and of the acquihiring subgame whenever $v_a \ne v_s$.
--
--   In words: if the acquirer hires the employee, which happens when $v_a > v_s$, it does so through acquihiring; however, the employee always prefers direct hiring. Acquihiring lets the acquirer act as a monopsonist and pay only the wage floor, at the price of compensating the startup for its retention profit but not the employee for her private benefit.
--
--   **Formalization Note.** The acquirer's choice of mode is expressed by comparing its continuation payoffs, quantified over all continuation equilibria of both subgames; the payoffs are not taken as definitions but derived from the equilibrium predicates. At the knife edge $v_a = v_s$ the page says nothing about hiring and clauses 1–2 are silent; clause 3 holds there too. Clause 4 is added so that clauses 1–3 are not vacuously true; it reflects the page's "which happens when $v_a > v_s$".
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 6 (PDF 7), Proposition 1

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model

namespace AcquihiringMonopsony.Baseline

/-- Proposition 1 (p. 6). Fix any continuation equilibrium `σD` of the direct-hiring subgame and
any continuation equilibrium `σA` of the acquihiring subgame.
1. If `v_a > v_s`, the acquirer hires the employee through acquihiring: the bid is accepted, and
   acquihiring gives the acquirer a strictly larger payoff than direct hiring.
2. If `v_a < v_s`, the acquirer does not hire the employee by either mode.
3. The employee strictly prefers the direct-hiring outcome to the acquihiring outcome.
4. Continuation equilibria of both subgames exist (away from the knife edges
   `v_a = v_s + b` and `v_a = v_s` respectively), so 1–3 are not vacuous. -/
theorem proposition_1 (P : Params) (hP : P.Standing)
    (σD : DHProfile) (hD : IsDHEquilibrium P σD) (σA : AHProfile) (hA : IsAHEquilibrium P σA) :
    (P.vs < P.va → σA.acceptBid σA.p = true ∧
      dhPayoffA P σD.acceptA σD.wa σD.ws < ahPayoffA P σA σA.p) ∧
    (P.va < P.vs → σA.acceptBid σA.p = false ∧ σD.acceptA σD.wa σD.ws = false) ∧
    ahPayoffE P σA < dhPayoffE P σD.acceptA σD.wa σD.ws ∧
    ((P.va ≠ P.vs + P.b → ∃ σ : DHProfile, IsDHEquilibrium P σ) ∧
      (P.va ≠ P.vs → ∃ σ : AHProfile, IsAHEquilibrium P σ)) := by sorry

end AcquihiringMonopsony.Baseline
