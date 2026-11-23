-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_star_algebraMap
-- name    : Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.star_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:25.357925+00:00
-- url     : https://prove2.me/theorems/6f6f955a-27b9-4a96-95fa-b55c5c846c7a
-- title:
--   Quadratic Extension Conjugation: star algebra Map
-- statement:
--   The Quadratic Extension Conjugation construction uses the star algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L24-L26

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

theorem Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.star_algebraMap (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (u : F) :
    star (algebraMap F K u) = algebraMap F K u := by sorry
