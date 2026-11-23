-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_chi_mul
-- name    : Formalism.UG.P.fIwasawa_chi_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:29.983725+00:00
-- url     : https://prove2.me/theorems/774becae-fc03-4905-b6b6-76b1a5628425
-- title:
--   P: f Iwasawa chi mul
-- statement:
--   The P construction uses the f Iwasawa chi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawa.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawa.lean#L68-L84

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)

theorem Formalism.UG.P.fIwasawa_chi_mul (hα : ∀ i, α i ≠ 0) (hq : (q : ℂ) ≠ 0) (b c : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    chiDeltaU q α (b * c) = chiDeltaU q α b * chiDeltaU q α c := by sorry
