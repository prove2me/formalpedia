-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_form_add_smul_left
-- name    : Formalism.FourierDecayAlt.P5.form_add_smul_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:40:29.61198+00:00
-- url     : https://prove2.me/theorems/c340fdac-bb14-43da-85f3-e1bd6ced5ad4
-- title:
--   P5: form add smul left
-- statement:
--   The P5 construction uses the form add smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsInnerAddSmulRight.lean#L60-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsInnerAddSmulRight.lean#L60-L83

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P5.form_add_smul_left (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u u' y : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u' b) (y b) (glue i c c'))) :
    form μ i (u + a • u') y c = form μ i u y c + a * form μ i u' y c := by sorry
