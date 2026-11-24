-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_init_basis
-- name    : Formalism.GM.MeanGammaLemmas.init_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:42.959293+00:00
-- url     : https://prove2.me/theorems/3d692b84-80cb-4264-be40-3098abb0f781
-- title:
--   Mean Gamma Lemmas: init basis
-- statement:
--   The Mean Gamma Lemmas construction uses the init basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L92-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L92-L146

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

theorem Formalism.GM.MeanGammaLemmas.init_basis {ι : Type} (f : ι → MvPolynomial σ ℚ_[p]) (ord : ι → ℕ) (v : σ)
    (Fil : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hord : ∀ b, HasOrder v (ord b) (f b))
    (hfil : ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = Fil e)
    (hstep : ∀ e x, x ∈ Fil e → initPart v e x = 0 → x ∈ Fil (e + 1)) (e : ℕ) :
    LinearIndepOn ℤ_[p] (fun b => initPart v e (f b)) {b | ord b = e} ∧
      Submodule.span ℤ_[p] ((fun b => initPart v e (f b)) '' {b | ord b = e}) =
        Submodule.span ℤ_[p] (initPart v e '' (Fil e : Set (MvPolynomial σ ℚ_[p]))) := by sorry
