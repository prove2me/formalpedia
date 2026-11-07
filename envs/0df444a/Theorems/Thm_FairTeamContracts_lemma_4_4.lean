-- Prove2me | Theorems.Thm_FairTeamContracts_lemma_4_4
-- name    : FairTeamContracts.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:54.0791+00:00
-- url     : https://prove2.me/theorems/9331c64e-11b4-4d6d-96c4-ecd59750c5a4
-- title:
--   Lemma 4.4 — two-agent fair teams lose at most a factor $1+\rho$ (additive)
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $\rho\in(0,1)$ satisfy $\rho^3-\rho^2-2\rho+1=0$ ($\rho\approx0.445$). Let $f$ be additive. Then every fair team contract $(S,\alpha)$ with $|S|=2$ satisfies
--
--   $$\mathrm{Rev}(S,\alpha)\ \le\ (1+\rho)\,\mathrm{OPT}_{nd}.$$
--
--   In particular, if an optimal fair contract has a two-agent team, the loss of non-discrimination $\mathrm{OPT}/\mathrm{OPT}_{nd}$ is at most $1+\rho$. This is the case in which the worst-case factor of Theorem 4.1 is attained.
--
--   Differences from the source:
--   - generalization: the optimal fair contract (S*, α*) with |S*| = 2 → every fair (S, α) with |S| = 2; reason: the proof uses only the minimum-share structure of S (Theorem 3.2), not optimality; specializes to (S*, α*)
--   - encoding: the loss of non-discrimination OPT/OPT_nd is at most 1 + ρ → rev f S α ≤ (1 + ρ) · optND f c; reason: multiplied out, no division by OPT_nd
--   - encoding: ρ ∈ (0, 1), the unique root of ρ³ − ρ² − 2ρ + 1 = 0 → any ρ ∈ (0, 1) with ρ³ − ρ² − 2ρ + 1 = 0; reason: uniqueness is clause 1 of Theorem 4.1; the statement holds for the unique root
--   - encoding: OPT, OPT_nd the revenues of optimal fair / non-discriminatory contracts → suprema optFair, optND over fair / feasible non-discriminatory team contracts; reason: the sets are nonempty and bounded by 1, so the suprema equal the optima, which exist
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 4.4, p.15 (proof: pp.15–16)

import Mathlib
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsAdditive
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_rev
import Definitions.Def_FairTeamContracts_optND

namespace FairTeamContracts

/-- **Lemma 4.4** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 4.4, p.15; proof pp.15–16). Let `ρ ∈ (0, 1)` be a
root of `ρ³ − ρ² − 2ρ + 1 = 0`. For an additive success function and nonnegative costs, every
fair team contract `(S, α)` with `|S| = 2` has revenue at most `(1 + ρ) · OPT_nd`: the loss of
non-discrimination is at most `1 + ρ` when the fair team has two agents.

**Formalization Note.** The paper states this for the optimal fair contract `(S*, α*)` with
`|S*| = 2`; the statement here holds for every fair contract with a two-agent team, and
specializes to `(S*, α*)`. The bound `OPT/OPT_nd ≤ 1 + ρ` is written multiplicatively. The
paper's scaling `f(S*) = 1` is a proof device, not a hypothesis. -/
theorem lemma_4_4 (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hcubic : ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0)
    {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsSuccessFn f) (hadd : IsAdditive f) (hc : ∀ i, 0 ≤ c i)
    (S : Finset (Fin n)) (α : Fin n → ℝ) (hfair : IsFair f c S α) (hcard : S.card = 2) :
    rev f S α ≤ (1 + ρ) * optND f c := by sorry

end FairTeamContracts
