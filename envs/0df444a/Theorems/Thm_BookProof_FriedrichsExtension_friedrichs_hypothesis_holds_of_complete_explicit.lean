-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_hypothesis_holds_of_complete_explicit
-- name    : BookProof.FriedrichsExtension.friedrichs_hypothesis_holds_of_complete_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:51.01821+00:00
-- url     : https://prove2.me/theorems/3f50b02d-74c8-46bc-ae16-32c9d60d0960
-- title:
--   Friedrichs' hypothesis, as a universal statement over densely defined positive symmetric operators
-- statement:
--   The assumption of the Friedrichs theorem holds with no side conditions on the operator: for every pair $(D', H')$ consisting of a dense subspace $D' \subseteq F$ and a symmetric operator $H' \colon D' \to F$ whose quadratic form is non-negative on $D'$, there are a domain $\mathrm{Dom} \subseteq F$ and a positive self-adjoint extension $A$ of $H'$.
--
--   In other words the Friedrichs hypothesis is not a restriction on the class of operators — positivity plus dense symmetric domain is enough — which is what lets the Yang–Mills, Navier–Stokes and fermionic Fock bundles invoke the extension theorem without an extra well-posedness assumption.
--
--   Corrected statement of the retired node `BookProof.FriedrichsExtension.friedrichs_hypothesis_holds`: completeness of $F$ is now an explicit binder, so the exported target no longer claims the result for incomplete spaces.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterFriedrichsExtension/Part2.lean

-- Corrected statement of BookProof.FriedrichsExtension.friedrichs_hypothesis_holds.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/Toolbox/ChapterFriedrichsExtension.lean (Lean 4.28) and timepiece331/BookProof/ChapterFriedrichsExtension/Part2.lean (Lean 4.33.1).
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FriedrichsExtension.friedrichs_hypothesis_holds_of_complete_explicit [CompleteSpace F] : ∀ (D' : Submodule ℂ F) (H' : D' →ₗ[ℂ] F), Dense (D' : Set F) → SymmetricOn D' H' → (∀ x : D', 0 ≤ quadForm H' x) → ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H' A := by sorry
