-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_core
-- name    : Formalism.EigenvalueLevelCeiling.gg_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:36.472834+00:00
-- url     : https://prove2.me/theorems/749b46f0-e298-48d2-90fb-6e874eeb1eee
-- title:
--   Eigenvalue Level Ceiling: gg core
-- statement:
--   The Eigenvalue Level Ceiling construction uses the gg core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L55-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L55-L114

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
variable {R : Type*} [CommRing R] {Y Q : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup Q]
  [Module R Q]

theorem Formalism.EigenvalueLevelCeiling.gg_core {Z : Type*} [AddCommGroup Z] [Module R Z] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : R) (A A' C B B' : Submodule R Z) (s t : ι → Z →ₗ[R] Z)
    (hsA : ∀ i, ∀ a ∈ A, s i a ∈ B) (hsA' : ∀ i, ∀ a ∈ A', s i a ∈ B')
    (htB : ∀ i, ∀ b ∈ B, t i b ∈ A) (htB' : ∀ i, ∀ b ∈ B', t i b ∈ A')
    (hts : ∀ i j, ∀ a ∈ A, t i (s j a) = if i = j then n • a else 0)
    (hC : ∀ c ∈ C, c ∈ A → ∃ a ∈ A, c = n • a) :
    (Fintype.card ι : ℕ∞) * Module.length R (A ⧸ A'.comap A.subtype) ≤
      Module.length R (B ⧸ B'.comap B.subtype) +
        (Fintype.card ι : ℕ∞) * Module.length R (A ⧸ C.comap A.subtype) := by sorry
