-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_herm_bvec_right
-- name    : Formalism.QuantumDeterminants.gn_herm_bvec_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:41.835899+00:00
-- url     : https://prove2.me/theorems/83ec9edd-c812-462d-b74d-fd289029f75e
-- title:
--   Quantum Determinants: gn herm bvec right
-- statement:
--   The Quantum Determinants construction uses the gn herm bvec right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L174-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L174-L182

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.gn_herm_bvec_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (j : Fin m) :
    herm H v (bvec j) = (H *ᵥ v) j := by sorry
