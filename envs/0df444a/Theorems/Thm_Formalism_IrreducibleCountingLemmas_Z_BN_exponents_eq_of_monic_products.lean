-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exponents_eq_of_monic_products
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.exponents_eq_of_monic_products
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:39.97868+00:00
-- url     : https://prove2.me/theorems/d6cae265-8d76-40da-9d81-24dee8691db3
-- title:
--   BN: exponents eq of monic products
-- statement:
--   The BN construction uses the exponents eq of monic products property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L117-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L117-L195

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN

theorem Formalism.IrreducibleCountingLemmas.Z.BN.exponents_eq_of_monic_products {K Γ ι : Type} [Field K] (t : Finset ι) (f : ι → Γ → K[X])
    (hm : ∀ i ∈ t, ∀ g, (f i g).Monic)
    (hli : ∀ c : ι → K, (∀ g, ∑ i ∈ t, c i * (f i g).nextCoeff = 0) → ∀ i ∈ t, c i = 0) :
    ∀ (N : ℕ) (a b : ι → ℕ), ∑ i ∈ t, (a i + b i) ≤ N →
      (∀ g, ∏ i ∈ t, f i g ^ a i = ∏ i ∈ t, f i g ^ b i) → ∀ i ∈ t, a i = b i := by sorry
