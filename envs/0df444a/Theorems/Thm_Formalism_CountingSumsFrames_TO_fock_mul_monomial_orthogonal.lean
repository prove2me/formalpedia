-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_mul_monomial_orthogonal
-- name    : Formalism.CountingSumsFrames.TO.fock_mul_monomial_orthogonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:34.428795+00:00
-- url     : https://prove2.me/theorems/8a87de55-83a7-470d-9ef8-1f2e10f02eb1
-- title:
--   TO: fock mul monomial orthogonal
-- statement:
--   The TO construction uses the fock mul monomial orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1293-L1313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1293-L1313

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

theorem Formalism.CountingSumsFrames.TO.fock_mul_monomial_orthogonal (j0 : ℕ) (s t : Finset (Fin N × Fin r →₀ ℕ)) (cg cg' : (Fin N × Fin r →₀ ℕ) → ℚ_[p])
    (hs : ∀ a ∈ s, ∀ v, a v ≠ 0 → fsj N r j0 v) (ht : ∀ b ∈ t, ∀ v, b v ≠ 0 → fsj N r j0 v)
    (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p ((∑ a ∈ s, monomial a (cg a)) * monomial m 1) ((∑ b ∈ t, monomial b (cg' b)) * monomial m' 1) =
      if m = m' then fock p (∑ a ∈ s, monomial a (cg a)) (∑ b ∈ t, monomial b (cg' b)) *
        (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by sorry
