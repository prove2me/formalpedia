-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_sum_eq_geoS
-- name    : Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.sum_eq_geoS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:55.01194+00:00
-- url     : https://prove2.me/theorems/259ce91f-ae73-4202-b5cd-03192b0bc653
-- title:
--   Cuspidal Irreducible Subrep: sum eq geo S
-- statement:
--   The Cuspidal Irreducible Subrep construction uses the sum eq geo S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L53-L64

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

theorem Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.sum_eq_geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (t : ℂ) :
    ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) = ρ ⬝ᵥ (geoS X t *ᵥ B) := by sorry
