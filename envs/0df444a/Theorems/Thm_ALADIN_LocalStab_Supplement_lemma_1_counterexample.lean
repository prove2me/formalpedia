-- Prove2me | Theorems.Thm_ALADIN_LocalStab_Supplement_lemma_1_counterexample
-- name    : ALADIN.LocalStab.Supplement.lemma_1_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:10:29.763316+00:00
-- url     : https://prove2.me/theorems/034c523d-ad33-4dd9-8ffd-98e742791eec
-- title:
--   Lemma 1 (corrected: counterexample) — a unit duality gap for every positive rho
-- statement:
--   Consider $\min u^2$ subject to $v=0$ and $u^2+v^2\ge1$, with identity scaling and center $\bar x=(0,1)$. The data are smooth, the objective Hessian is bounded, all original local minima are regular, and both global projection minimizers $(\pm1,0)$ are regular with equality multiplier $1$ and inequality multiplier $1/2$. Nevertheless, for every $\rho>0$,
--   $$\sup_\lambda V_\rho(\bar x,\lambda)=\rho,\qquad Z_\rho(\bar x)=\rho+1.$$
--   Thus the printed assumptions of Lemma 1 do not imply no duality gap, even if regularity is required of every projection minimizer. The theorem is a counterexample target; its draft proof is open. The finite-dimensional calculation and projection witnesses are retained in DISPROOF.md.
--
--   Differences from the source:
--   - correction: The source asserts eventual zero duality gap under regular projection-minimizer hypotheses. → The concrete instance has gap 1 for every positive rho and all projection minimizers regular.; reason: The dual upper bound from the two poles is attained at lambda=rho, while either feasible endpoint has proximal value rho+1.
--   - encoding: Finite real block vectors and the source optimization problems. → The published Fin-indexed carrier, explicit one-norm and quadratic forms, and extended-real value infima.; reason: Preserves the base definitions and avoids total real infimum defaults; counterexample data are explicit.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), DOI 10.1137/140975991, p. 1115, Lemma 1; explicit counterexample, see local DISPROOF.md

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Supplement_Countermodels

namespace ALADIN.LocalStab.Supplement

/-- Lemma 1, p.1115, is false without a substantive further hypothesis.
Both global projections of north are regular; bounded constraint Hessians do not fix the gap. -/
theorem lemma_1_counterexample :
    SmoothRegularProblem diskProblem ∧ BoundedObjectiveHessians diskProblem ∧
    (∀ i, (diskScaling i).PosDef) ∧
    GlobalMin (projectionProblem diskProblem diskScaling north) east ∧
    (projectionProblem diskProblem diskScaling north).IsRegularKKTPoint
      east (fun _ => 1) (fun _ _ => 1/2) ∧
    (∀ z, GlobalMin (projectionProblem diskProblem diskScaling north) z →
      (z = east ∨ z = west) ∧
      (projectionProblem diskProblem diskScaling north).IsRegularKKTPoint
        z (fun _ => 1) (fun _ _ => 1/2)) ∧
    ∀ ρ : ℝ, 0 < ρ →
      (⨆ lam : Fin 1 → ℝ, dualValue diskProblem diskScaling ρ north lam) = (ρ : EReal) ∧
      primalValue diskProblem diskScaling ρ north = ((ρ + 1 : ℝ) : EReal) := by sorry

end ALADIN.LocalStab.Supplement
