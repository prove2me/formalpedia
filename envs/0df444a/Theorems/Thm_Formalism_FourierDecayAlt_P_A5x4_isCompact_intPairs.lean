-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isCompact_intPairs
-- name    : Formalism.FourierDecayAlt.P.A5x4.isCompact_intPairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:10.137258+00:00
-- url     : https://prove2.me/theorems/bb0e1a00-8568-46be-ac12-b03c79536dd4
-- title:
--   A5x4: is Compact int Pairs
-- statement:
--   The A5x4 construction uses the is Compact int Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L13-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L13-L81

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Supp

theorem Formalism.FourierDecayAlt.P.A5x4.isCompact_intPairs {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (R : Subring K) (hRc : IsCompact (R : Set K)) (s : List ℕ) (t : ℕ → Kˣ) :
    IsCompact {p : lowW K s t × upUniG K s.sum |
      IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))} := by sorry
