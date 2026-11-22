-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_bvec_right
-- name    : Formalism.QuantumDeterminants.ggHerm_bvec_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:09.084198+00:00
-- url     : https://prove2.me/theorems/167f0c15-d092-4e8f-8908-2be794263828
-- title:
--   Quantum Determinants: gg Herm bvec right
-- statement:
--   The Quantum Determinants construction uses the gg Herm bvec right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L141-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L141-L150

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.ggHerm_bvec_right {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (v : ι → ℂ)
    (i : ι) : herm H v (Pi.single i 1) = (H *ᵥ v) i := by sorry
