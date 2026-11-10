-- Prove2me | Theorems.Thm_BilatMatch_lemma_B_5
-- name    : BilatMatch.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:10:56.467084+00:00
-- url     : https://prove2.me/theorems/30e7e338-c2b4-44a8-8b10-425c8c8d61b0
-- title:
--   Lemma B.5 (Convergence of Projected First Best) — $\mathrm{FB}_n\uparrow\mathrm{FB}$
-- statement:
--   Fix a matching environment with finitely many agents and downward-closed feasibility, with any independent priors. Let $I_n=[L_n,U_n]$ be nested common clipping intervals whose projections $\Pi_n$ converge to the identity on the original type supports. Then the first-best values $\mathrm{FB}_n$ of the projected markets increase to $\mathrm{FB}$:
--   $$\mathrm{FB}_n\le\mathrm{FB}_{n+1},\qquad \mathrm{FB}_n\to\mathrm{FB}.$$
--
--   **Formalization Note** Convergence of $\Pi_n$ to the identity is required only almost everywhere under each agent's prior. Limits are in $[0,\infty]$; no finiteness of $\mathrm{FB}$ is needed.
--
--   Differences from the source:
--   - generalization: projections converge to the identity on the original type supports → Π_n(t) → t for almost every type t of each agent's prior; reason: convergence at every point of the support implies almost-everywhere convergence, so the Lean hypothesis is weaker
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.5, p.34 (pdf p.36)

import Mathlib
import Definitions.Def_BilatMatch_rounding
import Definitions.Def_BilatMatch_FB

open MeasureTheory

namespace BilatMatch

/-- **Lemma B.5 (Convergence of Projected First Best).** Liu, Qin, Wang, arXiv:2609.30702 (held
version, sha256 ff1490ad…), Lemma B.5, p.34 (pdf p.36).

Fix a matching environment with finitely many agents and downward-closed feasibility. Let
`I_n = [L_n, U_n]` be nested common clipping intervals whose projections `Π_n` converge to the
identity on the original type supports. Then the first-best values `FB_n` of the projected markets
increase to `FB`.

**Formalization Note** "Converge to the identity on the original type supports" is taken as
convergence `Π_n(t) → t` for almost every type `t` of each agent's prior. "Increase to" is
monotonicity in `n` together with convergence in `ℝ≥0∞` (no finiteness of `FB` is needed). -/
theorem lemma_B_5 {B S : Type*} [Fintype B] [Fintype S] (I : Market B S) (hI : I.IsValid)
    (L U : ℕ → ℝ) (hLU : ∀ n, L n ≤ U n) (hL : Antitone L) (hU : Monotone U)
    (hconv : ∀ u, ∀ᵐ t ∂(I.law u),
      Filter.Tendsto (fun n => proj (L n) (U n) t) Filter.atTop (nhds t)) :
    Monotone (fun n => FB (I.projected (L n) (U n))) ∧
      Filter.Tendsto (fun n => FB (I.projected (L n) (U n))) Filter.atTop (nhds (FB I)) := by sorry

end BilatMatch
