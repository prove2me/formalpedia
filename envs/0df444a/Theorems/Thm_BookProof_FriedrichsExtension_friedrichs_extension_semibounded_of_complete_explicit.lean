-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_semibounded_of_complete_explicit
-- name    : BookProof.FriedrichsExtension.friedrichs_extension_semibounded_of_complete_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:46.305067+00:00
-- url     : https://prove2.me/theorems/5038444f-21b9-4112-91bf-bd9b2874a8c1
-- title:
--   Friedrichs extension of a semibounded symmetric operator
-- statement:
--   Let $H \colon D \to F$ be symmetric on a dense subspace $D \subseteq F$ and suppose its quadratic form is bounded below by $-c$: $\langle H x, x\rangle \ge -c\,\|x\|^2$ for every $x \in D$.  Then $H$ has a self-adjoint extension $A$ with the same lower bound $c$.
--
--   The proof shifts $H$ by $c + 1$, which makes the shifted form strictly positive and reduces the claim to the positive Friedrichs theorem; subtracting the shift returns the lower bound.  This is the classical form of the theorem used for Schrödinger-type operators.
--
--   Corrected statement of the retired node `BookProof.FriedrichsExtension.friedrichs_extension_of_semibounded_below`, with the completeness hypothesis carried explicitly.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterFriedrichsExtension/Part2.lean

-- Corrected statement of BookProof.FriedrichsExtension.friedrichs_extension_of_semibounded_below.
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

theorem BookProof.FriedrichsExtension.friedrichs_extension_semibounded_of_complete_explicit {D : Submodule ℂ F} [CompleteSpace F] (H : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D H) (c : ℝ) (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsSemiboundedSelfAdjointExtension c H A := by sorry
