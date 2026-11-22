-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_borel_tMat
-- name    : Formalism.UG.P.fSatake_borel_tMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:42.707605+00:00
-- url     : https://prove2.me/theorems/a9a8a446-9de6-42d6-b6b2-8bb3a2bfd8fb
-- title:
--   P: f Satake borel t Mat
-- statement:
--   The P construction uses the f Satake borel t Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L33-L36

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

theorem Formalism.UG.P.fSatake_borel_tMat {ϖ : L} {m : ℕ} {a : Fin m → ℤ} {t : GU σ n} (ht : ⟪t⟫ = tMat ϖ n m a) :
    IsBorelU t := by sorry
