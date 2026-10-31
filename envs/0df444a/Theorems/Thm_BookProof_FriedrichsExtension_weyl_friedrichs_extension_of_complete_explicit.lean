-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_weyl_friedrichs_extension_of_complete_explicit
-- name    : BookProof.FriedrichsExtension.weyl_friedrichs_extension_of_complete_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:50.677497+00:00
-- url     : https://prove2.me/theorems/95e5ffe8-30cd-4cd5-8b6e-e593d93ad714
-- title:
--   Friedrichs extension of the Weyl-gauge Yang–Mills operator
-- statement:
--   Let $D \subseteq F$ be dense, let $\pi_i, B_a$ be finitely many operators on $D$ that are symmetric on $D$ (the momentum/field operators of the Weyl-gauge slice), and let $\mathrm{weylOp}(\pi, B)$ be the associated Weyl-form operator on $D$.  Then $\mathrm{weylOp}(\pi, B)$ has a positive self-adjoint extension in $F$.
--
--   Symmetry of all the displayed pieces is what makes the quadratic form real-valued, and positivity of that form is the hypothesis the Friedrichs construction consumes; the Weyl-gauge Yang–Mills Hamiltonian is the operator obtained by restricting this extension to the gauge-invariant subspace.
--
--   Corrected statement of the retired node `BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional`, with `[CompleteSpace F]` explicit in the binder list.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterFriedrichsExtension/Part2.lean

-- Corrected statement of BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional.
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

theorem BookProof.FriedrichsExtension.weyl_friedrichs_extension_of_complete_explicit {D : Submodule ℂ F} [CompleteSpace F] {n m : ℕ} {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D} (hdense : Dense (D : Set F)) (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i))) (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension (weylOp pi Bf) A := by sorry
