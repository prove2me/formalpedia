-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_pow_mem_of_pos
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.pow_mem_of_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:16.684498+00:00
-- url     : https://prove2.me/theorems/2fed6171-2e08-4afb-b411-ebe3ab009fe2
-- title:
--   Hensel Roots Bounded: pow mem of pos
-- statement:
--   The Hensel Roots Bounded construction uses the pow mem of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L570-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L570-L574

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.pow_mem_of_pos (h : Ctx K R ϖ) {k : ℤ} (hk : 0 ≤ k) {x : K} (hx : x ∈ Pk R ϖ k) {m : ℕ}
    (hm : 1 ≤ m) : x ^ m ∈ Pk R ϖ k := by sorry
