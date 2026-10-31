-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists_of_complete_explicit
-- name    : BookProof.FriedrichsExtension.friedrichs_extension_exists_of_complete_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:08.135384+00:00
-- url     : https://prove2.me/theorems/6949e145-0049-4f65-816c-215212c4373f
-- title:
--   Friedrichs extension of a densely defined positive symmetric operator
-- statement:
--   Every densely defined symmetric operator $H$ on a complex Hilbert space $F$ with non-negative quadratic form has a positive self-adjoint extension: there are a domain $\mathrm{Dom} \subseteq F$ and an operator $A \colon \mathrm{Dom} \to F$ with $A \supseteq H$ that is self-adjoint and satisfies $\langle A x, x\rangle \ge 0$.
--
--   The construction is the one of Friedrichs: the form $\langle H x, x\rangle$ closes on the form domain to an inner product, Riesz representation gives the resolvent $S = (H + 1)^{-1}$ on the completed form space, and the extension is realised as the inverse-shifted operator $S^{-1} - 1$.  Form-domination of $F$ by the graph norm of $S$ is exactly the point at which the completeness of $F$, carried here as the explicit binder `[CompleteSpace F]`, is used: an incomplete $F$ need not contain the range of $S$.
--
--   This is the corrected statement of the retired node `BookProof.FriedrichsExtension.friedrichs_extension_exists`, whose exported target silently quantified over incomplete inner product spaces.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterFriedrichsExtension/Part2.lean

-- Corrected statement of BookProof.FriedrichsExtension.friedrichs_extension_exists.
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

theorem BookProof.FriedrichsExtension.friedrichs_extension_exists_of_complete_explicit (P : PosSymOp F) [CompleteSpace F] (hdense : Dense (P.dom : Set F)) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension P.op A := by sorry
