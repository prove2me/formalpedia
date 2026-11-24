-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_bord
-- name    : Formalism.IncomingBounds.Cay.bord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:36.392516+00:00
-- url     : https://prove2.me/theorems/fb6191ae-79c6-456d-bb40-c2a26ba86606
-- title:
--   Cay: bord
-- statement:
--   The Cay construction uses the bord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L83-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L83-L123

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix

theorem Formalism.IncomingBounds.Cay.bord {R : Type*} [CommRing R] (k : ℕ) (B : Matrix (Fin (k+2)) (Fin (k+2)) R) (j : Fin (k+2)) :
    ∑ q : Fin (k+1), ∑ p : Fin (k+1),
        adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 * B j q.succ
      = B j 0 * (B.submatrix j.succAbove Fin.succ).det - (-1) ^ (j : ℕ) * B.det := by sorry
