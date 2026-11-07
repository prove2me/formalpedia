-- Prove2me | Theorems.Thm_FairTeamContracts_lemma_4_6
-- name    : FairTeamContracts.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:13.135599+00:00
-- url     : https://prove2.me/theorems/76ed9810-0263-4557-a1b6-511c583c49e8
-- title:
--   Lemma 4.6 — fair teams of three or more agents lose at most $24/17<1+\rho$ (additive)
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $f$ be additive. Every fair team contract $(S,\alpha)$ with $|S|\ge3$ satisfies
--
--   $$\mathrm{OPT}_{nd}\ \ge\ \frac{17}{24}\,\mathrm{Rev}(S,\alpha).$$
--
--   Consequently, if an optimal fair contract has at least three agents, $\mathrm{OPT}/\mathrm{OPT}_{nd}\le 24/17$, and $24/17<1+\rho$ for the root $\rho\in(0,1)$ of $\rho^3-\rho^2-2\rho+1=0$. Large fair teams therefore never realize the worst case of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: the optimal fair contract (S*, α*) with |S*| ≥ 3 → every fair (S, α) with |S| ≥ 3; reason: the proof uses only the minimum-share structure of S (Theorem 3.2), not optimality; specializes to (S*, α*)
--   - encoding: OPT_nd ≥ (17/24) OPT; consequently OPT/OPT_nd ≤ 24/17 → (17/24) · rev f S α ≤ optND f c; reason: the consequence is the same inequality divided by OPT_nd; no division in Lean
--   - encoding: ρ ∈ (0, 1), the unique root of ρ³ − ρ² − 2ρ + 1 = 0 → any ρ ∈ (0, 1) with ρ³ − ρ² − 2ρ + 1 = 0; reason: uniqueness is clause 1 of Theorem 4.1; the statement holds for the unique root
--   - encoding: OPT, OPT_nd the revenues of optimal fair / non-discriminatory contracts → suprema optFair, optND over fair / feasible non-discriminatory team contracts; reason: the sets are nonempty and bounded by 1, so the suprema equal the optima, which exist
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 4.6, p.17 (proof: pp.17–19)

import Mathlib
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsAdditive
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_rev
import Definitions.Def_FairTeamContracts_optND

namespace FairTeamContracts

/-- **Lemma 4.6** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 4.6, p.17; proof pp.17–19). For an additive success
function and nonnegative costs, every fair team contract `(S, α)` with `|S| ≥ 3` satisfies
`OPT_nd ≥ (17/24) · Rev(S, α)`. Consequently the loss of non-discrimination on such teams is at
most `24/17`, and `24/17 < 1 + ρ` for the root `ρ ∈ (0, 1)` of `ρ³ − ρ² − 2ρ + 1 = 0`.

**Formalization Note.** The paper states the bound for the optimal fair contract `(S*, α*)` with
`|S*| ≥ 3`; the statement here holds for every fair contract with at least three agents, and
specializes to `(S*, α*)`. "Consequently, `OPT/OPT_nd ≤ 24/17`" is the first clause rewritten
multiplicatively (no division by `OPT_nd`); the clause `24/17 < 1 + ρ` is stated for every root
`ρ ∈ (0, 1)` of the cubic. -/
theorem lemma_4_6 :
    (∀ {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
      IsSuccessFn f → IsAdditive f → (∀ i, 0 ≤ c i) →
      ∀ (S : Finset (Fin n)) (α : Fin n → ℝ), IsFair f c S α → 3 ≤ S.card →
        (17 / 24 : ℝ) * rev f S α ≤ optND f c) ∧
    (∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 → ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0 → (24 / 17 : ℝ) < 1 + ρ) := by sorry

end FairTeamContracts
