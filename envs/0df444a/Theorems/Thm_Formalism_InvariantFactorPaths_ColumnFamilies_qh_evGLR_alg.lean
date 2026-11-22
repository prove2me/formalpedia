-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_alg
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:14.52397+00:00
-- url     : https://prove2.me/theorems/dc06085b-c9b8-47f5-a1d4-ea162473f9b6
-- title:
--   Column Families: qh ev GLR alg
-- statement:
--   The Column Families construction uses the qh ev GLR alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L24-L29

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
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
variable {n : ℕ} {R : Type} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_alg {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) R) :
    evGLR g (algebraMap _ (GLCoord R n) P) =
      MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P := by sorry
