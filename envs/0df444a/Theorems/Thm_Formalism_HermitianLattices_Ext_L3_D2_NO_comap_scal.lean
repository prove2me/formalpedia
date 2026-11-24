-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_comap_scal
-- name    : Formalism.HermitianLattices.Ext.L3.D2.NO.comap_scal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:40.346597+00:00
-- url     : https://prove2.me/theorems/7dec65e8-a013-4b39-82f5-f680f02acd71
-- title:
--   NO: comap scal
-- statement:
--   The NO construction uses the comap scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L286-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L286-L315

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO

theorem Formalism.HermitianLattices.Ext.L3.D2.NO.comap_scal {κ : Type} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (hπ0 : algebraMap F K (π : F) ≠ 0) (k c : ℕ) (f g d : κ → κ → K)
    (hf : ∀ i j, f i j ≠ 0)
    (hd : ∀ i j, f i j * d i j = g i j * algebraMap F K (π : F) ^ c) :
    (matL 𝔭 (k + c) f g).comap (scal κ 𝔭 (algebraMap F K (π : F) ^ k)) =
      AddSubgroup.pi Set.univ
        (fun p : κ × κ => (zR 𝔭 (d p.1 p.2)).addSubgroupOf (pK K 𝔭 0).toAddSubgroup) := by sorry
