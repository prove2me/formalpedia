-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_paired_sum_exp_bound
-- name    : Formalism.HermitianLatticeCounting.P.paired_sum_exp_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:39.834435+00:00
-- url     : https://prove2.me/theorems/c280fe59-67bc-4c6a-8617-feed60e75804
-- title:
--   P: paired sum exp bound
-- statement:
--   The P construction uses the paired sum exp bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L346-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L346-L374

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset

theorem Formalism.HermitianLatticeCounting.P.paired_sum_exp_bound {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (I I' : Finset ι) (J : Finset κ) (N : ι → ℝ)
    (D t : κ → ℝ) (φ : ι → κ) (B : ℝ) (c : ℕ) (hsub : I' ⊆ I) (hφ : ∀ i ∈ I', φ i ∈ J)
    (hinj : Set.InjOn φ (I' : Set ι)) (hN : ∀ i ∈ I, 0 ≤ N i)
    (hp : ∀ i ∈ I', N i ≤ Real.exp (t (φ i)) * D (φ i)) (hB : ∀ i ∈ I \ I', N i ≤ B)
    (hB1 : 1 ≤ B) (hc : (I \ I').card ≤ c) (hD : ∀ a ∈ J, 1 ≤ D a) (ht : ∀ a ∈ J, 0 ≤ t a) :
    ∏ i ∈ I, N i ≤ B ^ c * Real.exp (∑ a ∈ J, t a) * ∏ a ∈ J, D a := by sorry
