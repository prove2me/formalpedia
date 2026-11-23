-- Prove2me | Theorems.Thm_Formalism_F_gram_intMatrix_eq_map
-- name    : Formalism.F.gram_intMatrix_eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:42.294489+00:00
-- url     : https://prove2.me/theorems/151f717f-adfb-411f-8d40-c3dc5423577d
-- title:
--   F: gram int Matrix eq map
-- statement:
--   The F construction uses the gram int Matrix eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopesBdd.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopesBdd.lean#L49-L54

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u

theorem Formalism.F.gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by sorry
