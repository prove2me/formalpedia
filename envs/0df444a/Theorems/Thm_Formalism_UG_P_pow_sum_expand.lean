-- Prove2me | Theorems.Thm_Formalism_UG_P_pow_sum_expand
-- name    : Formalism.UG.P.pow_sum_expand
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:45.80105+00:00
-- url     : https://prove2.me/theorems/4078b5a4-8e74-40ae-ac66-0e6a97364d22
-- title:
--   P: pow sum expand
-- statement:
--   The P construction uses the pow sum expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L22-L30

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.pow_sum_expand (a b : n → MvPolynomial n O) (K : ℕ) :
    (∑ j, C (a j) * map C (b j) : MvPolynomial n (MvPolynomial n O)) ^ K
      = ∑ β ∈ Finset.piAntidiag Finset.univ K,
          C ((Nat.multinomial Finset.univ β : MvPolynomial n O) * ∏ j, a j ^ β j) *
            map C (∏ j, b j ^ β j) := by sorry
