-- Prove2me | Theorems.Thm_Formalism_REAL_commutator_of_sums_split
-- name    : Formalism.REAL.commutator_of_sums_split
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:20:02.118917+00:00
-- url     : https://prove2.me/theorems/15755ad9-3ced-4e9f-86a4-a3a2eaa73aa5
-- title:
--   REAL: commutator of sums split
-- statement:
--   The REAL construction uses the commutator of sums split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L366-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L366-L401

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.commutator_of_sums_split {A : Type*} [Ring A] {ι : Type*} (s : Finset ι) (S T : ι → A) (P Q : A)
    (hST : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → S i * T i' = T i' * S i)
    (hSQ : ∀ i ∈ s, S i * Q = Q * S i) (hPT : ∀ i ∈ s, P * T i = T i * P) :
    (∑ i ∈ s, S i + P) * (∑ i ∈ s, T i + Q) - (∑ i ∈ s, T i + Q) * (∑ i ∈ s, S i + P) =
      ∑ i ∈ s, (S i * T i - T i * S i) + (P * Q - Q * P) := by sorry
