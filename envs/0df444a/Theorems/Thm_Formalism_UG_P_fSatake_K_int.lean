-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_K_int
-- name    : Formalism.UG.P.fSatake_K_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:53.228228+00:00
-- url     : https://prove2.me/theorems/d1fbde89-c1aa-495a-a166-43400edf4d03
-- title:
--   P: f Satake K int
-- statement:
--   The P construction uses the f Satake K int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L137-L141

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

theorem Formalism.UG.P.fSatake_K_int {k : GU σ n} (hk : k ∈ KU σ n) (i j : Fin n) : ⟪k⟫ i j ∈ intL L := by sorry
