-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_sig
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_sig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:07.822841+00:00
-- url     : https://prove2.me/theorems/faf58a54-f803-4eaf-b736-2e722ceba2c7
-- title:
--   Column Families: qd ev sig
-- statement:
--   The Column Families construction uses the qd ev sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L51-L61

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_sig {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) x (qd_sig n P) = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) P := by sorry
