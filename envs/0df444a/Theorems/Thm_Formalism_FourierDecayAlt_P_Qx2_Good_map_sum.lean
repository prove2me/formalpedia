-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
-- name    : Formalism.FourierDecayAlt.P.Qx2.Good.map_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:11:04.832711+00:00
-- url     : https://prove2.me/theorems/6216cbe8-6007-40e1-97ea-6fdfd680380c
-- title:
--   Good: map sum
-- statement:
--   The Good construction uses the map sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L563-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L563-L574

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.Qx2.Good.map_sum {T : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (a : ℕ → ℂ)
    {c : ℕ → Mx k r → E} (hc : ∀ j, SmoothLev k r i D (c j)) {x : Mx k r} (hx : x ∈ Glev k r i ∩ D) (N : ℕ) :
    T (fun y => ∑ j ∈ Finset.range N, a j • c j y) x = ∑ j ∈ Finset.range N, a j • T (c j) x := by sorry
