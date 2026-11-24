-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_star_norm
-- name    : Formalism.InvariantFactorPaths.G7.StarEntryOperators.star_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:45.788136+00:00
-- url     : https://prove2.me/theorems/69d28992-bead-4f88-aacc-8af2679074e0
-- title:
--   Star Entry Operators: star norm
-- statement:
--   The Star Entry Operators construction uses the star norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L202-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLeOfDvd.lean#L202-L305

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators

theorem Formalism.InvariantFactorPaths.G7.StarEntryOperators.star_norm {K : Type} [NormedField K] [IsUltrametricDist K] (hS : StarArith)
    {p ν r0 r1 E : ℕ} [NeZero ν] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (TT : Finset (ZMod (2 * ν))) (e : TpV ν r1 → ℕ) (ls : ZMod (2 * ν) → ℕ)
    (he : ∀ x : TpV ν r1, x.1 ∉ TT → e x = 0) (β : KapI ν r1 E →₀ ℕ)
    (hβ : ∀ k, β k ≠ 0 → k.1 ∈ TT) (n : ZV ν r0 r1 →₀ ℕ) (i0 i2 : ℕ)
    (h1 : ∀ s, ∑ x : Fin r0 × Fin r1, n (s, x) ≤ ls s) (h2 : n.degree + ∑ k, β k = ∑ s, ls s)
    (h3 : ∀ k : KapI ν r1 E, p ^ (2 * k.2.1.val + 1) * β k ≤ e (k.1, k.2.2))
    (h4 : p * i2 ≤ n.degree) :
    (p : ℝ) ^ (i0 + ∑ k, β k + i2) * ‖((mfact (Finsupp.equivFunOnFinite.symm e) : ℕ) : K)‖ *
        ‖(((∑ k, β k).factorial : ℕ) : K)‖ * ‖((mfact n : ℕ) : K)‖ ≤
      (p : ℝ) ^ (-(gamP p * ∑ s ∈ TT, (alN e s : ℝ) - (i0 : ℝ) - (∑ k, (β k : ℝ)) -
        deLoss p r0 r1 TT (alN e) ls + rhoP p * ∑ s, ((alN e s : ℝ) + ls s))) := by sorry
