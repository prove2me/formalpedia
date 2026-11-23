-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_minor_lemma
-- name    : Formalism.FourierDecayAlt.P.A5x7.minor_lemma
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:27.617667+00:00
-- url     : https://prove2.me/theorems/8ff2d6e5-2137-4fb5-b2aa-c43163041b18
-- title:
--   A5x7: minor lemma
-- statement:
--   The A5x7 construction uses the minor lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L77-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L77-L177

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x7.minor_lemma {n m : ℕ} (hmn : m < n) (x w y : Matrix (Fin n) (Fin n) K)
    (H : Matrix (Fin m) (Fin m) K) (t : K) (hx : IsLowUni x) (hy : IsUpUni y)
    (hw1 : ∀ (a b : Fin n) (ha : a.val < m),
      w a b = if hb : b.val < m then H ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0)
    (hw2 : ∀ a b : Fin n, a.val = m → w a b = if b.val + 1 = n then t else 0)
    (hI : IsInt R (x * w * y)) : H.det * t ∈ R := by sorry
