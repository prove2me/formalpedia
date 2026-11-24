-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_cell_exists
-- name    : Formalism.UG.P.fSatake_cell_exists
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:05.369829+00:00
-- url     : https://prove2.me/theorems/79658c37-e9e0-4af8-a5b0-4c40375f2bc9
-- title:
--   P: f Satake cell exists
-- statement:
--   The P construction uses the f Satake cell exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L252-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L252-L361

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

theorem Formalism.UG.P.fSatake_cell_exists {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    (hm' : n ≤ 2 * m + 1) {b k : GU σ n} (hb : IsBorelU b) (hk : k ∈ KU σ n) :
    ∃ a : Fin m → ℤ, ∃ u : GU σ n, IsUnipU u ∧ ∃ k' ∈ KU σ n,
      ⟪b * k⟫ = tMat ϖ n m a * ⟪u⟫ * ⟪k'⟫ := by sorry
