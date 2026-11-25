-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_eta_lim
-- name    : Formalism.GM.leadingTermLemmas.fk_eta_lim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:18.417018+00:00
-- url     : https://prove2.me/theorems/1b05d770-a9da-4313-8347-f11d14156c2b
-- title:
--   leading Term Lemmas: fk eta lim
-- statement:
--   The leading Term Lemmas construction uses the fk eta lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1269-L1289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1269-L1289

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
open Filter Topology Finset

theorem Formalism.GM.leadingTermLemmas.fk_eta_lim {σ : Type} [Fintype σ] [DecidableEq σ] (i : σ) (S d : ℕ) (g g' : MvPolynomial σ ℝ)
    (hg : ∀ M ∈ g.support, M i ≤ d) :
    Tendsto (fun n : ℕ => fk (MvPolynomial.X i ^ (n - S) * g) (MvPolynomial.X i ^ (n - S) * g') /
        (((n - S).factorial : ℝ) * (n : ℝ) ^ d)) atTop
      (𝓝 (∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (if M i = d then 1 / (d.factorial : ℝ) else 0))) := by sorry
