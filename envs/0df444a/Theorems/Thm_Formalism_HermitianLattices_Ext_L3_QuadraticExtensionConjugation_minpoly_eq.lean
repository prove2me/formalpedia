-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_minpoly_eq
-- name    : Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.minpoly_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:09.641941+00:00
-- url     : https://prove2.me/theorems/f235e6bb-687e-491c-9e17-562bd38fd3b0
-- title:
--   Quadratic Extension Conjugation: minpoly eq
-- statement:
--   The Quadratic Extension Conjugation construction uses the minpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L112-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DifferentIdealEqTop.lean#L112-L162

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

theorem Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.minpoly_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (θ t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) (hne : θ ≠ t) :
    aeval θ (derivative (minpoly (𝓞 F) θ)) = θ - t := by sorry
