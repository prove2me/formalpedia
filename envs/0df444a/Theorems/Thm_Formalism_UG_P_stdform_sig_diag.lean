-- Prove2me | Theorems.Thm_Formalism_UG_P_stdform_sig_diag
-- name    : Formalism.UG.P.stdform_sig_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:13.318165+00:00
-- url     : https://prove2.me/theorems/ffd825f9-3a07-49e4-898b-c6afe3d856a5
-- title:
--   P: stdform sig diag
-- statement:
--   The P construction uses the stdform sig diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stdform.lean#L182-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stdform.lean#L182-L203

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.stdform_sig_diag {p q : ℕ} (M : Matrix n n ℂ) (e : n ≃ Fin p ⊕ Fin q)
    (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * M.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q) (y : n → ℂ) :
    ∃ x : Fin p ⊕ Fin q → ℂ, (y ≠ 0 → x ≠ 0) ∧
      stdformQ M y = (∑ i, Complex.normSq (x (Sum.inl i))) - ∑ j, Complex.normSq (x (Sum.inr j)) := by sorry
