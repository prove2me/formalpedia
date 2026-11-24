-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_adjoin_eq_top
-- name    : Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.adjoin_eq_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:55.503136+00:00
-- url     : https://prove2.me/theorems/d8477ab7-1d67-4e5b-9b09-6a33ad61582b
-- title:
--   Quadratic Extension Conjugation: adjoin eq top
-- statement:
--   The Quadratic Extension Conjugation construction uses the adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L74-L80

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

theorem Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.adjoin_eq_top (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) : Algebra.adjoin F {a} = ⊤ := by sorry
