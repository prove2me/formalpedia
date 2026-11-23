-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_pow_diff
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.pow_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:14.462808+00:00
-- url     : https://prove2.me/theorems/30932aa9-e529-4b29-8fcb-522df4508179
-- title:
--   Hensel Roots Bounded: pow diff
-- statement:
--   The Hensel Roots Bounded construction uses the pow diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L257-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L257-L265

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.pow_diff (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) (s : ℕ) {w w' : K} (hw : w ∈ Pk R ϖ n)
    (hw' : w' ∈ Pk R ϖ n) :
    ∃ g ∈ Pk R ϖ n, (1 + w') ^ s - (1 + w) ^ s = (w' - w) * ((s : K) + g) := by sorry
