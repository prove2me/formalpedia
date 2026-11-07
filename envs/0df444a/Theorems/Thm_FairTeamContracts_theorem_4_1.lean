-- Prove2me | Theorems.Thm_FairTeamContracts_theorem_4_1
-- name    : FairTeamContracts.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:53.819126+00:00
-- url     : https://prove2.me/theorems/b0f7fa92-3c82-4718-8637-82dd53162b88
-- title:
--   Theorem 4.1 — tight loss of non-discrimination $1+\rho$, $\rho^3-\rho^2-2\rho+1=0$, for additive and submodular rewards
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $\mathrm{OPT}_{nd}$ and $\mathrm{OPT}$ be the optimal revenue of non-discriminatory and of fair team contracts. Then:
--
--   1. the equation $\rho^3-\rho^2-2\rho+1=0$ has a unique root $\rho\in(0,1)$ ($\rho\approx0.445$);
--   2. for every additive $f$ and all costs $c\ge0$,
--   $$\mathrm{OPT}_{nd}\ \ge\ \frac{1}{1+\rho}\,\mathrm{OPT};$$
--   3. the same holds for every submodular $f$;
--   4. the factor $1+\rho$ is tight for both classes: there is an instance, additive and submodular, with $\mathrm{OPT}>0$ and $\mathrm{OPT}=(1+\rho)\,\mathrm{OPT}_{nd}$.
--
--   Restricting a principal to equal shares therefore costs at most a factor $1+\rho\approx1.445$ of the best fair revenue, and no smaller factor is valid.
--
--   Differences from the source:
--   - encoding: OPT_nd ≥ OPT/(1 + ρ) → optFair f c ≤ (1 + ρ) · optND f c; reason: multiplied by 1 + ρ > 0
--   - reading: this approximation factor 1 + ρ is tight → an instance, additive and submodular, with 0 < OPT and OPT = (1 + ρ) · OPT_nd; reason: the strongest reading of tightness: the factor is attained, so no smaller factor is valid
--   - encoding: ρ ∈ (0, 1) is the unique root, used in the bound → clause ∃! ρ ∈ (0, 1) with the cubic = 0, and the bounds for every such ρ; reason: the same ρ by uniqueness
--   - encoding: submodular (Definition 2.4, for every i ∈ [n]) → published IsSubmodular (diminishing returns for e ∉ B) together with the monotonicity of IsSuccessFn; reason: Definition 2.4's extra cases i ∈ S′ only say a marginal is ≥ 0, which is monotonicity; same class of functions
--   - encoding: OPT, OPT_nd the revenues of optimal fair / non-discriminatory contracts → suprema optFair, optND over fair / feasible non-discriminatory team contracts; reason: the sets are nonempty and bounded by 1, so the suprema equal the optima, which exist
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 4.1, p.13 (proof: pp.15–19)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsAdditive
import Definitions.Def_FairTeamContracts_optFair
import Definitions.Def_FairTeamContracts_optND

namespace FairTeamContracts

/-- **Theorem 4.1 (Tight loss of non-discrimination)** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 4.1, p.13;
proof pp.15–19). Let `OPT_nd` and `OPT` be the optimal revenue of non-discriminatory and of fair
team contracts. Then:

1. the cubic `ρ³ − ρ² − 2ρ + 1 = 0` has a unique root `ρ ∈ (0, 1)`;
2. for that `ρ`, every additive success function and nonnegative costs give
   `OPT_nd ≥ OPT/(1 + ρ)`;
3. the same holds for every monotone, normalized, submodular success function;
4. the factor `1 + ρ` is tight for both classes: some instance, additive and submodular, has
   `OPT > 0` and `OPT = (1 + ρ) · OPT_nd`.

**Formalization Note.** The inequality is written `OPT ≤ (1 + ρ) · OPT_nd`. OPT and OPT_nd are
suprema over fair, resp. feasible non-discriminatory, team contracts (see `optFair`, `optND`).
The bounds quantify over every `n`, every success function of the class and every cost vector
`c ≥ 0`. Tightness is stated with equality and `OPT > 0`, so no factor below `1 + ρ` is valid. -/
theorem theorem_4_1 :
    (∃! ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 ∧ ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0) ∧
    ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 → ρ ^ 3 - ρ ^ 2 - 2 * ρ + 1 = 0 →
      (∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f → IsAdditive f →
        (∀ i, 0 ≤ c i) → optFair f c ≤ (1 + ρ) * optND f c) ∧
      (∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f →
        SubsamplingSM.Offline.IsSubmodular f → (∀ i, 0 ≤ c i) → optFair f c ≤ (1 + ρ) * optND f c) ∧
      (∃ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f ∧ IsAdditive f ∧
        SubsamplingSM.Offline.IsSubmodular f ∧ (∀ i, 0 ≤ c i) ∧
        0 < optFair f c ∧ optFair f c = (1 + ρ) * optND f c) := by sorry

end FairTeamContracts
