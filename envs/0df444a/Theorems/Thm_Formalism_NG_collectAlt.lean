-- Prove2me | Theorems.Thm_Formalism_NG_collectAlt
-- name    : Formalism.NG.collectAlt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:20.747839+00:00
-- url     : https://prove2.me/theorems/e8247a28-f2c4-4367-8233-9ba278d821de
-- title:
--   NG: collect Alt
-- statement:
--   The NG construction uses the collect Alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L33-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L33-L99

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelsOfBlockChiCOfBlockChiOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.collectAlt (t : ℕ) (ht : 1 ≤ t) (L : Fin (t + 1) → ℕ∞) (S : Finset (Fin (t + 1))) (v : ℕ∞)
    (what₂ cols qs : Finset ℕ) (lenRow vζ h0 : ℕ → ℕ∞) (e' j deg : ℕ → ℕ) (Sha : ℕ → ℕ∞)
    (eO vδ s vhE N H0 : ℕ∞) (cB : ℕ)
    (hG : v ≤ ∑ k ∈ S, L k)
    (hL0 : L 0 ≤ ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) +
      s + 4 * N * ((cols.card : ℕ∞) + 1) * vδ)
    (hL1 : L ⟨1, by omega⟩ ≤ vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      ∑ w ∈ qs, vζ w)
    (hLc : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) → L c ≤ Sha ((c : ℕ) - 1) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w) :
    v ≤ ∑ w ∈ what₂, lenRow w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, vζ w := by sorry
