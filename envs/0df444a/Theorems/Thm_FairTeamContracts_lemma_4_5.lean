-- Prove2me | Theorems.Thm_FairTeamContracts_lemma_4_5
-- name    : FairTeamContracts.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:40.02593+00:00
-- url     : https://prove2.me/theorems/b1307ca8-d75d-4a8a-9c52-6d953331c247
-- title:
--   Lemma 4.5 — a two-agent additive instance with $\mathrm{OPT}_{nd}\le\mathrm{OPT}/(1+\rho)$
-- statement:
--   Let $\rho\in(0,1)$ satisfy $\rho^3-\rho^2-2\rho+1=0$. Consider two agents $a,b$, the additive success function with
--
--   $$f(a)=\rho,\qquad f(b)=1-\rho,\qquad f(\{a,b\})=1,$$
--
--   and the costs $c_a=\rho^3/(1+\rho)$, $c_b=\rho(1-\rho)/(1+\rho)$. This is a success function, additive and submodular, with nonnegative costs, and
--
--   $$\mathrm{OPT}>0,\qquad \mathrm{OPT}_{nd}\ \le\ \frac{1}{1+\rho}\,\mathrm{OPT}.$$
--
--   Together with the upper bound of Theorem 4.1 it shows that the factor $1+\rho$ cannot be improved, for additive and for submodular rewards.
--
--   Differences from the source:
--   - generalization: there exists an instance for additive rewards with OPT_nd ≤ OPT/(1 + ρ) → the explicit instance of the proof (f(a) = ρ, f(b) = 1 − ρ, c_a = ρ³/(1+ρ), c_b = ρ(1−ρ)/(1+ρ)), shown to be a submodular additive success function with c ≥ 0 and 0 < OPT; reason: a named witness is stronger than existence; 0 < OPT keeps the bound from holding vacuously at OPT = 0
--   - encoding: OPT_nd ≤ OPT/(1 + ρ) → (1 + ρ) · optND f c ≤ optFair f c; reason: multiplied by 1 + ρ > 0
--   - encoding: ρ ∈ (0, 1), the unique root of ρ³ − ρ² − 2ρ + 1 = 0 → any ρ ∈ (0, 1) with ρ³ − ρ² − 2ρ + 1 = 0; reason: uniqueness is clause 1 of Theorem 4.1; the statement holds for the unique root
--   - encoding: OPT, OPT_nd the revenues of optimal fair / non-discriminatory contracts → suprema optFair, optND over fair / feasible non-discriminatory team contracts; reason: the sets are nonempty and bounded by 1, so the suprema equal the optima, which exist
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 4.5, p.17 (proof: p.17)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsAdditive
import Definitions.Def_FairTeamContracts_optFair
import Definitions.Def_FairTeamContracts_optND

namespace FairTeamContracts

/-- **Lemma 4.5** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Lemma 4.5, p.17; proof p.17). Let `ρ ∈ (0, 1)` be a root
of `ρ³ − ρ² − 2ρ + 1 = 0`. The two-agent additive instance of the proof, with `f(a) = ρ`,
`f(b) = 1 − ρ` and costs `c_a = ρ³/(1 + ρ)`, `c_b = ρ(1 − ρ)/(1 + ρ)`, is a success function that is
additive and submodular, has nonnegative costs and `OPT > 0`, and satisfies
`OPT_nd ≤ OPT/(1 + ρ)`.

**Formalization Note.** The agents `a, b` are `0, 1 : Fin 2`. The paper states "there exists an
instance"; the statement gives the proof's explicit instance, and adds `0 < OPT` (in the proof
`OPT = 1 − ρ`), which keeps the bound from holding vacuously at `OPT = 0`. The inequality is
written multiplicatively. -/
theorem lemma_4_5 (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hcubic : ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0) :
    let f : Finset (Fin 2) → ℝ := fun S => ∑ i ∈ S, (![ρ, 1 - ρ] : Fin 2 → ℝ) i
    let c : Fin 2 → ℝ := ![ρ ^ 3 / (1 + ρ), ρ * (1 - ρ) / (1 + ρ)]
    IsSuccessFn f ∧ IsAdditive f ∧ SubsamplingSM.Offline.IsSubmodular f ∧ (∀ i, 0 ≤ c i) ∧
      0 < optFair f c ∧ (1 + ρ) * optND f c ≤ optFair f c := by sorry

end FairTeamContracts
