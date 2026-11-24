-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_mul_mono
-- name    : Formalism.CountingSumsFrames.TO.fock_mul_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:34.057815+00:00
-- url     : https://prove2.me/theorems/9fa96408-5fbd-4462-bab5-6fdc3d1e6d69
-- title:
--   TO: fock mul mono
-- statement:
--   The TO construction uses the fock mul mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1315-L1322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1315-L1322

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.fock_mul_mono (j0 : ℕ) {g g' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : IsF (fsj N r j0) g)
    (hg' : IsF (fsj N r j0) g') (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p (g * monomial m 1) (g' * monomial m' 1) =
      if m = m' then fock p g g' * (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by sorry
