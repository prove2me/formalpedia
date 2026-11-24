-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_exists_star_ne
-- name    : Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.exists_star_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:13.327923+00:00
-- url     : https://prove2.me/theorems/8e5a3c90-a005-46ed-b54a-a6a622e1a482
-- title:
--   Quadratic Extension Conjugation: exists star ne
-- statement:
--   The Quadratic Extension Conjugation construction uses the exists star ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L12-L22

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

theorem Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by sorry
