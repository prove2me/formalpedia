-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_scale
-- name    : Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:28:24.738487+00:00
-- url     : https://prove2.me/theorems/425ae2a4-b6f9-411c-b32b-26a3838e67e2
-- title:
--   Three Forms Alt: qlen scale
-- statement:
--   The Three Forms Alt construction uses the qlen scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L429-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L429-L474

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_scale [FiniteDimensional K Z] (hS : IdxScaleIn) (w : HeightOneSpectrum (𝓞 K))
    (W : Submodule K Z) (L : Submodule (𝓞 K) Z) (hL : IsLatIn W L) {a : K} (ha : a ≠ 0) (E : ℕ)
    (hE : vw w a = (E : ℤ)) :
    qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L) = ((E * finrank K W : ℕ) : ℕ∞) := by sorry
