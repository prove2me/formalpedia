-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_entry_deg
-- name    : Formalism.GM.MeanGammaLemmas.entry_deg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:41.330806+00:00
-- url     : https://prove2.me/theorems/5909c6e9-eaab-4502-af95-8afaa6931481
-- title:
--   Mean Gamma Lemmas: entry deg
-- statement:
--   The Mean Gamma Lemmas construction uses the entry deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L333-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L333-L343

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M

theorem Formalism.GM.MeanGammaLemmas.entry_deg (hDeg : GamDeg) {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r)
    (z e e' : ℕ) (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r)
    (hv : LLw.vec (Fin.last K) = true) (hf : f ∈ Pol p r LLw) (hf' : f' ∈ Pol p r LLw)
    (he : HasOrder (Fin.last K, ρ) e f) (he' : HasOrder (Fin.last K, ρ) e' f')
    (Q : ℚ_[p][X]) (a : ℚ_[p])
    (hQ : ∀ n : ℕ, LLw.total ≤ n → Q.eval (n : ℚ_[p]) = a * tieGam p LLw ρ z n f f') :
    Q.natDegree ≤ LLw.total + LLw.deg (Fin.last K) - max e e' := by sorry
