-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_discr_pos
-- name    : Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.discr_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:44.029477+00:00
-- url     : https://prove2.me/theorems/5d7c223d-c889-4955-a44d-112f03ca1b71
-- title:
--   Quadratic Extension Conjugation: discr pos
-- statement:
--   The Quadratic Extension Conjugation construction uses the discr pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L185-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L185-L192

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.discr_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : 0 < discr F := by sorry
