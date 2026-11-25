-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_main
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:23:01.107509+00:00
-- url     : https://prove2.me/theorems/8eb00daa-7b72-4e65-9747-f88cb82734fb
-- title:
--   Column Families: qn main
-- statement:
--   The Column Families construction uses the qn main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnEvalMap.lean#L60-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnEvalMap.lean#L60-L141

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_main (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) {ι : Type}
    (P : ι → MvPolynomial (Fin n × Fin n) ℤ) (i0 : ι)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν)
    (h2 : dualWeyl ℤ n n ν ≤ Submodule.span ℤ (Set.range fun i => transposeVariables ℤ n (P i)))
    (h3 : eval (idFrame ℤ n n) (transposeVariables ℤ n (P i0)) = 1) :
    (Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))
          (map (Int.castRingHom ℚ) (P i0))} := by sorry
