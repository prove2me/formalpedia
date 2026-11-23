-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_ggE_mem_eig
-- name    : Formalism.EigenvalueLevelCeiling.ggE_mem_eig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:58.107453+00:00
-- url     : https://prove2.me/theorems/daad4531-9b75-45a6-abd7-43e60e257580
-- title:
--   Eigenvalue Level Ceiling: gg E mem eig
-- statement:
--   The Eigenvalue Level Ceiling construction uses the gg E mem eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L141-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L141-L154

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem Formalism.EigenvalueLevelCeiling.ggE_mem_eig {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) (hMk : IsMackey U ψ) (x : Z) : ggE ρ U ψ x ∈ eig ρ U ψ := by sorry
