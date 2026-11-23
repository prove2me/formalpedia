-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_det_sigma_reindexed_square_block
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.det_sigma_reindexed_square_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:55.17487+00:00
-- url     : https://prove2.me/theorems/d51b65b6-621e-49ad-be85-18ffef5db5f4
-- title:
--   Height Descent Minors: det sigma reindexed square block
-- statement:
--   The Height Descent Minors construction uses the det sigma reindexed square block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1524-L1541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1524-L1541

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {R : Type} [CommRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.det_sigma_reindexed_square_block {n : ℕ} (Φ : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (I : Finset ℕ)
    (tt : ↥I → ℕ) (F G : ∀ r : ↥I, Fin (tt r) → {j // b j = r.1}) (r : ↥I) :
    ((Φ.submatrix (fun x : (Σ r : ↥I, Fin (tt r)) => (F x.1 x.2).1)
        (fun x : (Σ r : ↥I, Fin (tt r)) => (G x.1 x.2).1)).toSquareBlock
          (fun x : (Σ r : ↥I, Fin (tt r)) => x.1.1) r.1).det =
      ((Φ.toSquareBlock b r.1).submatrix (F r) (G r)).det := by sorry
