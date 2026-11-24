-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_sesquilinear_polarization
-- name    : Formalism.FourierDecayAlt.P5.sesquilinear_polarization
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:41:58.06887+00:00
-- url     : https://prove2.me/theorems/87178914-7d93-4654-96ca-62763d08bfcd
-- title:
--   P5: sesquilinear polarization
-- statement:
--   The P5 construction uses the sesquilinear polarization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L126-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L126-L132

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

theorem Formalism.FourierDecayAlt.P5.sesquilinear_polarization {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    4 * β x y = β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) + Complex.I * β (x + Complex.I • y) (x + Complex.I • y)
      - β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) - Complex.I * β (x + (-Complex.I) • y) (x + (-Complex.I) • y) := by sorry
