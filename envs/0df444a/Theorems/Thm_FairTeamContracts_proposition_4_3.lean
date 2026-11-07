-- Prove2me | Theorems.Thm_FairTeamContracts_proposition_4_3
-- name    : FairTeamContracts.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:29.161142+00:00
-- url     : https://prove2.me/theorems/f86d7282-5309-4e38-ae3a-4ed7938f1187
-- title:
--   Proposition 4.3 — reduction of submodular to additive fair contracts
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $\Gamma>0$ and fix the agent set $N=[n]$. Suppose that for every additive success function $f$ on $N$ and all costs $c\ge0$, the optimal non-discriminatory contract achieves at least a $1/\Gamma$ fraction of the optimal fair revenue, $\mathrm{OPT}\le\Gamma\cdot\mathrm{OPT}_{nd}$. Then the same guarantee holds for every submodular success function on $N$ and all costs $c\ge0$:
--
--   $$\mathrm{OPT}\ \le\ \Gamma\cdot\mathrm{OPT}_{nd}.$$
--
--   The reduction transfers any additive guarantee for the loss of non-discrimination to submodular rewards, and gives the submodular half of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: the guarantee for every additive reward function (any number of agents) → the guarantee only for additive instances on the same agent set Fin n; reason: a weaker hypothesis; the proof builds the additive instance on the same agents; specializes to the page's claim
--   - encoding: OPT_nd achieves at least a 1/Γ fraction of OPT → optFair f c ≤ Γ · optND f c with 0 < Γ; reason: multiplied by Γ > 0, which '1/Γ fraction' presupposes
--   - encoding: submodular (Definition 2.4, for every i ∈ [n]) → published IsSubmodular (diminishing returns for e ∉ B) together with the monotonicity of IsSuccessFn; reason: Definition 2.4's extra cases i ∈ S′ only say a marginal is ≥ 0, which is monotonicity; same class of functions
--   - encoding: OPT, OPT_nd the revenues of optimal fair / non-discriminatory contracts → suprema optFair, optND over fair / feasible non-discriminatory team contracts; reason: the sets are nonempty and bounded by 1, so the suprema equal the optima, which exist
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Proposition 4.3, p.13 (proof: pp.14–15)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsAdditive
import Definitions.Def_FairTeamContracts_optFair
import Definitions.Def_FairTeamContracts_optND

namespace FairTeamContracts

/-- **Proposition 4.3 (Reduction to additive fair contracts)** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…),
Proposition 4.3, p.13; proof pp.14–15). Suppose that for every additive reward function, the
optimal non-discriminatory contract achieves at least a `1/Γ` fraction of the optimal fair
contract. Then the same guarantee holds for every submodular reward function.

**Formalization Note.** The agent set `Fin n` is fixed: the hypothesis on every additive instance
on `Fin n` (with nonnegative costs) gives the conclusion on every submodular instance on `Fin n`.
This is stronger than quantifying the hypothesis over all `n`. `Γ > 0`, and "at least a `1/Γ`
fraction" is written `OPT ≤ Γ · OPT_nd`. -/
theorem proposition_4_3 (n : ℕ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hadd : ∀ (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f → IsAdditive f →
      (∀ i, 0 ≤ c i) → optFair f c ≤ Γ * optND f c) :
    ∀ (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsSuccessFn f →
      SubsamplingSM.Offline.IsSubmodular f → (∀ i, 0 ≤ c i) → optFair f c ≤ Γ * optND f c := by sorry

end FairTeamContracts
