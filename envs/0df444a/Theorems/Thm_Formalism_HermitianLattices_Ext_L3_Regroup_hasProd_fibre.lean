-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Regroup_hasProd_fibre
-- name    : Formalism.HermitianLattices.Ext.L3.Regroup.hasProd_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:19.364824+00:00
-- url     : https://prove2.me/theorems/9c0881c7-d4c2-4d5f-9ea7-b55530cdada2
-- title:
--   Regroup: has Prod fibre
-- statement:
--   The Regroup construction uses the has Prod fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LValEtaEqLValEtaF.lean#L23-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LValEtaEqLValEtaF.lean#L23-L98

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.Regroup
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.Regroup.hasProd_fibre (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 1 ≤ M)
    (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    HasProd (fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1)
      (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by sorry
