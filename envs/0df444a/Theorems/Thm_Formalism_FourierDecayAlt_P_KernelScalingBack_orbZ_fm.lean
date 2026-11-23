-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_orbZ_fm
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.orbZ_fm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:19.972455+00:00
-- url     : https://prove2.me/theorems/47ac7dfd-7f3c-4c2e-8de6-c55632add3dd
-- title:
--   Kernel Scaling Back: orb Z fm
-- statement:
--   The Kernel Scaling Back construction uses the orb Z fm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L148-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L148-L161

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.orbZ_fm (p : lowW K S T × upUniG K S.sum) :
    orbZ ((S, T * c) : Point K) (fm S T c p) = orbZ ((S, T) : Point K) p *
      ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) := by sorry
