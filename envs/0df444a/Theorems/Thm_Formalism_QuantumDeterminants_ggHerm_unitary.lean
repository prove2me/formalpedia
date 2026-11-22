-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_unitary
-- name    : Formalism.QuantumDeterminants.ggHerm_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:47.8872+00:00
-- url     : https://prove2.me/theorems/4f57dde5-c312-470b-852c-b8c53f98a0d4
-- title:
--   Quantum Determinants: gg Herm unitary
-- statement:
--   The Quantum Determinants construction uses the gg Herm unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L136-L139

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

theorem Formalism.QuantumDeterminants.ggHerm_unitary {ι : Type*} [Fintype ι] (H g : Matrix ι ι ℂ) (hg : gᴴ * H * g = H)
    (v w : ι → ℂ) : herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by sorry
