-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Step_tendsto_left
-- name    : Formalism.HermitianLattices.Ext.L3.Step.tendsto_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:40.846793+00:00
-- url     : https://prove2.me/theorems/6e7fa029-e907-5da8-a0e6-a394aef9a479
-- title:
--   Step: tendsto left
-- statement:
--   The Step construction uses the tendsto left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassConstSucc.lean#L51-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassConstSucc.lean#L51-L70

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepMassEqProdPsi
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoBallCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSingSSum
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassRatioEqLvalue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LamGEqOneOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FactorIdentity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassConstSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
open Formalism.HermitianLattices.Ext.L3.Step
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.Step.tendsto_left (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Tendsto (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (Formalism.HermitianLatticesTheory.mass h L *
        ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
          (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L)))) := by sorry
