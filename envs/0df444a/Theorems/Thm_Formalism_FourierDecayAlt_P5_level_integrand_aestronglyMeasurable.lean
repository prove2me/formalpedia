-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_level_integrand_aestronglyMeasurable
-- name    : Formalism.FourierDecayAlt.P5.level_integrand_aestronglyMeasurable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:43:03.375911+00:00
-- url     : https://prove2.me/theorems/4d678085-4779-41ac-b15c-12ad2953433e
-- title:
--   P5: level integrand aestrongly Measurable
-- statement:
--   The P5 construction uses the level integrand aestrongly Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L185-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L185-L197

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem Formalism.FourierDecayAlt.P5.level_integrand_aestronglyMeasurable (hM : TopDensMeas S P z z' π π' μ L st K) (w : List (Letter ℂ S))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K (Fin.last P.r)) x) (hy : InK (K (Fin.last P.r)) y)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) :
    AEStronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w x y (glue i c q.1) (Matrix.of q.2)) (volume.prod μ) := by sorry
