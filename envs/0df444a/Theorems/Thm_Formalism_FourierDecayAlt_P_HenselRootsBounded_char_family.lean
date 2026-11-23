-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_char_family
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.char_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:15.43781+00:00
-- url     : https://prove2.me/theorems/6c2e37b8-f31c-4a5d-bab9-7e79fa5c57f6
-- title:
--   Hensel Roots Bounded: char family
-- statement:
--   The Hensel Roots Bounded construction uses the char family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L384-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L384-L431

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.char_family {K : Type} [CommRing K] (B B' : AddSubgroup K)
    (hfin : Finite (B ⧸ B'.addSubgroupOf B)) :
    ∃ S : Finset K, S.card ≠ 0 ∧ (∀ b ∈ S, b ∈ B) ∧ ∀ χ : AddChar K ℂ, (∀ b ∈ B', χ b = 1) →
      (∃ b ∈ B, χ b ≠ 1) → ∑ b ∈ S, χ b = 0 := by sorry
