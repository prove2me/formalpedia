-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_FE_one
-- name    : Formalism.GM.leadingTermLemmas.FE_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:52.718817+00:00
-- url     : https://prove2.me/theorems/39b9495a-614b-4eaf-980c-75f20810fe19
-- title:
--   leading Term Lemmas: FE one
-- statement:
--   The leading Term Lemmas construction uses the FE one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L290-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L290-L293

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe

theorem Formalism.GM.leadingTermLemmas.FE_one {a b : ℕ} {g : MvPolynomial σ K} (hg : BiHom w e a b g) :
    tieF w e (tieE w e g) = tieE w e (tieF w e g) + ((a + b + r : ℕ) : K) • g := by sorry
