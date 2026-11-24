-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_prod_pow
-- name    : Formalism.GM.leadingTermLemmas.biHom_prod_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:24.616583+00:00
-- url     : https://prove2.me/theorems/14429f0c-b9d9-4f20-8a5e-13c1fc764b50
-- title:
--   leading Term Lemmas: bi Hom prod pow
-- statement:
--   The leading Term Lemmas construction uses the bi Hom prod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L800-L808
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L800-L808

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
variable {K σ : Type} [Field K] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}

theorem Formalism.GM.leadingTermLemmas.biHom_prod_pow {ι : Type} [DecidableEq ι] (t : Finset ι) (g : ι → MvPolynomial σ K) (A B k : ι → ℕ)
    (hg : ∀ i ∈ t, BiHom w e (A i) (B i) (g i)) :
    BiHom w e (∑ i ∈ t, k i * A i) (∑ i ∈ t, k i * B i) (∏ i ∈ t, g i ^ k i) := by sorry
