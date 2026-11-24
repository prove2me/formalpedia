-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_omega_value
-- name    : Formalism.MainNotions.PlaneGram.omega_value
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:07:38.805357+00:00
-- url     : https://prove2.me/theorems/f4c8adc8-a2a9-4d68-96e0-5b0da2facd4d
-- title:
--   Plane Gram: omega value
-- statement:
--   The Plane Gram construction uses the omega value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/OmegaValue.lean#L12-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/OmegaValue.lean#L12-L106

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_OmegaValue
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem Formalism.MainNotions.PlaneGram.omega_value (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gp gm : D.EM → K) (hgp0 : ∀ ζ, 0 ≤ v (gp ζ))
    (happ : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZi : Integral v Z) (hZg : D.Good p Z) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (dg gp Z))) - D.abelian₂ p F Z) := by sorry
