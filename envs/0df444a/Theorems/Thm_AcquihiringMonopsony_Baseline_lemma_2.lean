-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Baseline_lemma_2
-- name    : AcquihiringMonopsony.Baseline.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:42.456177+00:00
-- url     : https://prove2.me/theorems/1ba6c7a8-0c7f-4c0b-8120-5348954c0237
-- title:
--   Lemma 2 — under acquihiring the bid v_s − w̲ is accepted if v_a > v_s, the bid fails if v_a < v_s; efficiency cases
-- statement:
--   Consider the baseline model with $b > 0$ and $\min\{v_a, v_s\} > b + \underline{w}$, and suppose the acquirer chooses acquihiring: it bids a price for the startup, and whichever firm then employs the worker makes her a wage offer.
--
--   In every continuation equilibrium in undominated strategies, with bid $p$:
--   1. if $v_a > v_s$, the acquirer bids $p = v_s - \underline{w}$, the bid is accepted, and the acquirer employs the worker at wage $\underline{w}$;
--   2. if $v_a < v_s$, the bid is declined and the startup retains the worker at wage $\underline{w}$.
--
--   Continuation equilibria exist in both cases, and when $v_a < v_s$ the bid $p = v_a - \underline{w}$ is an equilibrium bid. The outcome is efficient (total surplus equal to $\max\{v_a, v_s + b\}$) if $v_a \ge v_s + b$ or $v_a < v_s$, and inefficient, with surplus
--   $$
--   v_a < \max\{v_a,\ v_s + b\} = v_s + b,
--   $$
--   if $v_s < v_a < v_s + b$.
--
--   The acquirer only needs to compensate the startup for its retention profit $v_s - \underline{w}$, never the employee for her lost private benefit; this is what makes acquihiring attractive to the acquirer and harmful to the employee.
--
--   **Formalization Note.** When $v_a < v_s$ the equilibrium bid is not unique: every bid below $v_s - \underline{w}$ is declined and gives the acquirer $0$. The page's "the acquirer offers $p = v_a - \underline{w}$" is therefore stated as the existence of an equilibrium with that bid, while "the offer is declined" holds for every equilibrium.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), pp. 5–6 (PDF 6–7), Lemma 2

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model

namespace AcquihiringMonopsony.Baseline

/-- Lemma 2 (pp. 5–6): under acquihiring, in every continuation equilibrium, if `v_a > v_s` the
acquirer bids `v_s − w̲`, the bid is accepted and the acquirer pays the wage `w̲`; if
`v_a < v_s` the bid is declined and the startup pays the wage `w̲`. Continuation equilibria
exist in both cases, and when `v_a < v_s` the bid `v_a − w̲` is an equilibrium bid. The outcome
is efficient if `v_a ≥ v_s + b` or `v_a < v_s`, and inefficient if `v_s < v_a < v_s + b`. -/
theorem lemma_2 (P : Params) (hP : P.Standing) :
    (∀ σ : AHProfile, IsAHEquilibrium P σ →
      (P.vs < P.va → σ.p = P.vs - P.wl ∧ σ.acceptBid σ.p = true ∧ σ.wa = P.wl) ∧
      (P.va < P.vs → σ.acceptBid σ.p = false ∧ σ.ws = P.wl) ∧
      (P.va < P.vs → surplus P (σ.acceptBid σ.p) = max P.va (P.vs + P.b)) ∧
      (P.vs + P.b ≤ P.va → surplus P (σ.acceptBid σ.p) = max P.va (P.vs + P.b)) ∧
      (P.vs < P.va → P.va < P.vs + P.b →
        surplus P (σ.acceptBid σ.p) < max P.va (P.vs + P.b))) ∧
    (P.vs < P.va → ∃ σ : AHProfile, IsAHEquilibrium P σ) ∧
    (P.va < P.vs → ∃ σ : AHProfile, IsAHEquilibrium P σ ∧ σ.p = P.va - P.wl) := by sorry

end AcquihiringMonopsony.Baseline
