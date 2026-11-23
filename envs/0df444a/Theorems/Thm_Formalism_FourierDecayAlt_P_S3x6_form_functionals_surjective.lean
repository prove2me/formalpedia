-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_functionals_surjective
-- name    : Formalism.FourierDecayAlt.P.S3x6.form_functionals_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:01.513805+00:00
-- url     : https://prove2.me/theorems/a2539fde-8d01-4972-9247-76ef07dae420
-- title:
--   S3x6: form functionals surjective
-- statement:
--   The S3x6 construction uses the form functionals surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L224-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L224-L253

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.FourierDecayAlt.P.S3x6.form_functionals_surjective (hσ : Inv σ) (h : V →ₛₗ[σ] V →ₗ[K] K) (hn : Nondeg h) {ι : Type} [Fintype ι]
    [DecidableEq ι] (x : ι → V) (hx : LinearIndependent K x) (r : ι → K) :
    ∃ m, ∀ i, h (x i) m = r i := by sorry
