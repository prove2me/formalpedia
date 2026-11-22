-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_mid
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.col_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:19.518819+00:00
-- url     : https://prove2.me/theorems/c0becc8f-99ec-499e-bce5-49ab39783ac4
-- title:
--   Bruhat Big Cell: col mid
-- statement:
--   The Bruhat Big Cell construction uses the col mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L54-L58

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
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
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

theorem Formalism.QuantumDeterminants.BruhatBigCell.col_mid (i j : Fin (2 * r + k + 1)) (h1 : r ≤ j.val) (h2 : j.val ≤ r + k) :
    bigCell k r c μ i j = if hi : r ≤ i.val ∧ i.val ≤ r + k then
      μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0 := by sorry
