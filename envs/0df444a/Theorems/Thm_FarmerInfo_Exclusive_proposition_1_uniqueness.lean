-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_proposition_1_uniqueness
-- name    : FarmerInfo.Exclusive.proposition_1_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:48.97268+00:00
-- url     : https://prove2.me/theorems/4c34d2e1-6998-41b8-85d2-07166e39c2ac
-- title:
--   Proposition 1, pp. 12, 34 — every equilibrium equals the linear profile almost surely
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   For any informed set $I$ and every Bayesian Nash equilibrium $q$, each farmer’s realized quantity equals the linear profile of (6)–(7) almost surely:
--
--   $$q_i(\operatorname{obs}_i)=q_i^{\mathrm{lin}}(\operatorname{obs}_i)\quad\text{almost surely for every }i.$$
--
--   Thus equilibrium welfare does not depend on a selection among admissible equilibria.
--
--   **Formalization Note** Equality is almost sure, as stated in the proof on page 34, and ranges over all admissible strategies.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 12, Proposition 1; p. 34, Proof of Proposition 1

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Proposition 1, pp. 12, 34: every equilibrium agrees almost surely. -/
theorem proposition_1_uniqueness (M : Model) (hM : M.Standing) :
    ∀ (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy),
      M.IsBNE I σ →
      ∀ i : Fin M.n,
        (fun ω : M.Ω => σ i (M.obs I i ω)) =ᵐ[M.P]
          (fun ω : M.Ω => M.linProfile I i (M.obs I i ω)) := by sorry
end
end FarmerInfo.Exclusive
