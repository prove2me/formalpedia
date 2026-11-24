-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_ext_reduce
-- name    : Formalism.CountingSumsFrames.TO.fock_ext_reduce
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:34.664807+00:00
-- url     : https://prove2.me/theorems/830b1e8b-78ac-4e6d-b397-fb5ab1cd4fac
-- title:
--   TO: fock ext reduce
-- statement:
--   The TO construction uses the fock ext reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1324-L1362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1324-L1362

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
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

theorem Formalism.CountingSumsFrames.TO.fock_ext_reduce (j0 : ℕ)
    (A φ1 φ2 : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : ℚ_[p])
    (Cs : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hA : ∀ g q, IsL (fsj N r j0) q → A (g * q) = A g * q)
    (hAF : ∀ g, IsF (fsj N r j0) g → IsF (fsj N r j0) (A g))
    (h1 : ∀ x, IsF (fsj N r j0) (φ1 x)) (h2 : ∀ x, IsF (fsj N r j0) (φ2 x))
    (hcore : ∀ g ∈ Cs, ∀ g' ∈ Cs, fock p (A g) (φ1 g') = c * fock p (φ2 g) g')
    (u u' : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hu : ∀ m, slc (fsj N r j0) m u ∈ Cs)
    (hu' : ∀ m, slc (fsj N r j0) m u' ∈ Cs) :
    fock p (A u) (ext (fsj N r j0) φ1 u') = c * fock p (ext (fsj N r j0) φ2 u) u' := by sorry
