-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_lead_part
-- name    : Formalism.GM.MeanGammaLemmas.lead_part
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:03.630022+00:00
-- url     : https://prove2.me/theorems/62fb4065-9e57-4045-9204-42942e9acd6b
-- title:
--   Mean Gamma Lemmas: lead part
-- statement:
--   The Mean Gamma Lemmas construction uses the lead part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L400-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L400-L539

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

theorem Formalism.GM.MeanGammaLemmas.lead_part (hDeg : GamDeg) (hLead : GamLead) {p : ℕ} [hp : Fact p.Prime] {K r : ℕ} [NeZero r]
    (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (z : ℕ)
    (w : Fin r → ℤ) (n₀ : ℕ) (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ)
    (κ : ℝ) (m cI : ℕ) (cc : Fin n₀ → Fin n₀ → ℕ → ℤ_[p]) (hr1 : 1 ≤ r) (hv : LLw.vec (Fin.last K) = true)
    (hli : LinearIndependent ℤ_[p] f) (hspan : Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w)
    (hord : ∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b))
    (hfil : ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e)
    (hL4 : GramDeterminantGradedHypothesis p LLw J M ρ κ)
    (hcc : ∀ x y (n : ℕ), LLw.total ≤ n →
      ((p : ℚ_[p]) ^ cI) * tieGam p LLw ρ z n (f x) (f y) =
        ∑ i ∈ range (LLw.total + LLw.deg (Fin.last K) + 1), (cc x y i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])) :
    (∀ x y (n : ℕ), LLw.total ≤ n →
      ((binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)) x y).eval (n : ℚ_[p]) =
        (p : ℚ_[p]) ^ (m + cI) * tieGam p LLw ρ z n (f x) (f y)) ∧
    (binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)).det.natDegree =
      ∑ b, (LLw.total + LLw.deg (Fin.last K) - ord b) ∧
    ∏ b, (‖betaT p (m + cI) z (LLw.deg (Fin.last K)) LLw.total (ord b)‖ * (p : ℝ) ^ (-κ)) ≤
      ‖(binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)).det.leadingCoeff‖ ∧
    (∀ b, ord b ≤ LLw.deg (Fin.last K)) ∧ LLw.deg (Fin.last K) ≤ LLw.total := by sorry
