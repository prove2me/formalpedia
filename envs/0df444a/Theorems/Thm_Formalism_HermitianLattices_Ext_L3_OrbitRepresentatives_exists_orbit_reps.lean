-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_exists_orbit_reps
-- name    : Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.exists_orbit_reps
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:54:01.327378+00:00
-- url     : https://prove2.me/theorems/974e631b-48c7-4cef-9b78-d58a5cb72ca8
-- title:
--   Orbit Representatives: exists orbit reps
-- statement:
--   The Orbit Representatives construction uses the exists orbit reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardStabilizerAutSub.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardStabilizerAutSub.lean#L13-L35

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives

theorem Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.exists_orbit_reps {G X : Type*} [Group G] [MulAction G X] (A : Set X) (hfin : A.Finite)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by sorry
