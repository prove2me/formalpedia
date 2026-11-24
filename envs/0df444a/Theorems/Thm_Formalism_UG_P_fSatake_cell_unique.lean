-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_cell_unique
-- name    : Formalism.UG.P.fSatake_cell_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:16.743999+00:00
-- url     : https://prove2.me/theorems/51a103c2-fcf3-45e9-bd0f-44318699883d
-- title:
--   P: f Satake cell unique
-- statement:
--   The P construction uses the f Satake cell unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L412-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L412-L453

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem Formalism.UG.P.fSatake_cell_unique {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {a a' : Fin m → ℤ} {u u' k k' : GU σ n} (hu : IsUnipU u) (hu' : IsUnipU u')
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n)
    (h : tMat ϖ n m a * ⟪u⟫ * ⟪k⟫ = tMat ϖ n m a' * ⟪u'⟫ * ⟪k'⟫) : a = a' := by sorry
