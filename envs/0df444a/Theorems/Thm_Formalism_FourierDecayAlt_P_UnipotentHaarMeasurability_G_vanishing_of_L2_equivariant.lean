-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_G_vanishing_of_L2_equivariant
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.vanishing_of_L2_equivariant
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:57:26.664831+00:00
-- url     : https://prove2.me/theorems/328a5786-2268-5491-adc9-0954ecf6e055
-- title:
--   G: vanishing of L2 equivariant
-- statement:
--   The G construction uses the vanishing of L2 equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/VanishingOfL2Equivariant.lean#L17-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/VanishingOfL2Equivariant.lean#L17-L41

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_VanishingOfL2Equivariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_vanishing_of_L2_equivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 3200000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.vanishing_of_L2_equivariant {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hIn : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by sorry
