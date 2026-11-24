-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exponents_eq
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.exponents_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:55.754372+00:00
-- url     : https://prove2.me/theorems/9cb2da38-2477-4bef-9a51-64c1cdf8abcb
-- title:
--   BN: exponents eq
-- statement:
--   The BN construction uses the exponents eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L197-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L197-L202

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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.exponents_eq {K Γ ι : Type} [Field K] (t : Finset ι) (f : ι → Γ → K[X])
    (hm : ∀ i ∈ t, ∀ g, (f i g).Monic)
    (hli : ∀ c : ι → K, (∀ g, ∑ i ∈ t, c i * (f i g).nextCoeff = 0) → ∀ i ∈ t, c i = 0)
    (a b : ι → ℕ) (h : ∀ g, ∏ i ∈ t, f i g ^ a i = ∏ i ∈ t, f i g ^ b i) :
    ∀ i ∈ t, a i = b i := by sorry
