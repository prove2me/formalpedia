-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_exists_int_of_star_eq
-- name    : Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.exists_int_of_star_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:14.377013+00:00
-- url     : https://prove2.me/theorems/2edd1dc7-d5f2-4da2-a1b3-8e177fdb2daf
-- title:
--   Quadratic Extension Conjugation: exists int of star eq
-- statement:
--   The Quadratic Extension Conjugation construction uses the exists int of star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L86-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L86-L96

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

theorem Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.exists_int_of_star_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))
    (y : 𝓞 K) (hy : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y) :
    ∃ z : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) z = y := by sorry
