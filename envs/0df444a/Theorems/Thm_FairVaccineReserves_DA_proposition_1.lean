-- Prove2me | Theorems.Thm_FairVaccineReserves_DA_proposition_1
-- name    : FairVaccineReserves.DA.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:54:22.39206+00:00
-- url     : https://prove2.me/theorems/eb0834dc-3744-4db4-923c-3775c2795566
-- title:
--   Proposition 1 — Characterization by deferred acceptance
-- statement:
--   Fix finite patients $I$, finite categories $C$, natural quotas $r_c$, and an arbitrary independent strict priority order $\pi_c$ on $I\cup\{\varnothing\}$ for each category. Patient $i$ is eligible at $c$ if $i\pi_c\varnothing$. Let $\mu:I\to C\cup\{\varnothing\}$ satisfy $|\mu^{-1}(c)|\le r_c$ for every $c$.
--
--   Let $\mathcal P$ be all profiles of full strict artificial preferences with $c\succ_i\varnothing$ if and only if $i\pi_c\varnothing$. Let $\operatorname{DA}(R,\succ)$ be the actual simultaneous patient-proposing deferred-acceptance output, starting from empty holds and retaining the highest-priority quota-many incumbents and new applicants at each round. Then
--
--   $$
--   \begin{aligned}
--   &\bigl[(\forall i,c,\ \mu(i)=c\Rightarrow i\pi_c\varnothing)\\
--   &\quad\land(\forall i,c,\ i\pi_c\varnothing\ \land\ \mu(i)=\varnothing\Rightarrow |\mu^{-1}(c)|=r_c)\\
--   &\quad\land(\forall i,j,c,\ \mu(i)=c\ \land\ \mu(j)=\varnothing\Rightarrow i\pi_c j)\bigr]\\
--   &\hspace{2em}\Longleftrightarrow\ \exists\succ\in\mathcal P,\quad\operatorname{DA}(R,\succ)=\mu.
--   \end{aligned}
--   $$
--
--   This characterizes the whole assignment, including category labels. The priority comparison includes ineligible unmatched patients. Quotas may be zero, priorities need not share a baseline, and compatible preferences may differ across patients. Neither direction assumes algorithm correctness or a constructed realizing profile.
--
--   Differences from the source:
--   - encoding: arbitrary finite patient and category sets with a separate outside option → Fin n and Fin m, with Option for the outside option; reason: finite relabeling preserves every assignment and its category labels
--   - encoding: independent full strict priority orders and full artificial preference orders → bijections from each Option type to consecutive finite ranks, with smaller ranks better; reason: every finite strict linear order has exactly such a ranking, including all positions below the outside option
--   - encoding: q units and quotas whose sum is q → totalUnits is defined as the sum of the natural quotas; reason: q is determined by the quotas and does not otherwise occur in Proposition 1
--   - encoding: a matching in the capacity-feasible set M → the published Assignment function type with a separate CapacityFeasible hypothesis; reason: eligibility remains a conclusion clause rather than an assumption bundled in the matching type
--   - encoding: simultaneous DA stopping at a round with no rejections → sorted acceptable-list adapter to published DA, with permissible-pair fuel and stationary padding; reason: each productive round consumes a previously untried pair and a no-rejection round leaves every unheld patient exhausted, so the final assignment is unchanged
--   - generalization: finite populations in the allocation setting, with no explicit discussion of empty populations → also permits zero patients or zero categories; reason: the unique empty or all-unassigned output satisfies the same equivalence, and all source instances are retained
-- source:
--   Pathak, Sönmez, Ünver and Yenmez, arXiv:2008.00374v3 (1 July 2023; draft May 2023), https://arxiv.org/abs/2008.00374v3, Proposition 1, §3.5, printed/PDF p. 18; proof Appendix C.2, printed A.13–A.14 / PDF pp. 57–58

import Definitions.Def_FairVaccineReserves_DA_Axioms
import Definitions.Def_FairVaccineReserves_DA_Procedure

namespace FairVaccineReserves.DA

theorem proposition_1 {n m : ℕ} (R : ReserveSystem n m)
    (μ : GaleShapley1962.Admissions.Assignment n m)
    (hμ : R.CapacityFeasible μ) :
    (R.CompliesWithEligibility μ ∧ R.NonWasteful μ ∧ R.RespectsPriorities μ) ↔
      R.DAInduced μ := by sorry

end FairVaccineReserves.DA
