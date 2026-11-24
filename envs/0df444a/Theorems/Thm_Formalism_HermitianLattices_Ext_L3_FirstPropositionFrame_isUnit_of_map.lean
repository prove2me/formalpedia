-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FirstPropositionFrame_isUnit_of_map
-- name    : Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame.isUnit_of_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:48.782329+00:00
-- url     : https://prove2.me/theorems/0d2b46b1-bcaf-471c-bfa8-79edd9c409b8
-- title:
--   First Proposition Frame: is Unit of map
-- statement:
--   The First Proposition Frame construction uses the is Unit of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftUnimod.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftUnimod.lean#L13-L22

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame.isUnit_of_map (π : A →+* A') (hπ : Function.Surjective π)
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {u : A} (hu : IsUnit (π u)) :
    IsUnit u := by sorry
