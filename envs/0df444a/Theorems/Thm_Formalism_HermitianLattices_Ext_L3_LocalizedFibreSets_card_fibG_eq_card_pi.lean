-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_card_fibG_eq_card_pi
-- name    : Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.card_fibG_eq_card_pi
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:23:20.579171+00:00
-- url     : https://prove2.me/theorems/738e6637-2e2b-49a0-b81a-ef1bdf098aac
-- title:
--   Localized Fibre Sets: card fib G eq card pi
-- statement:
--   The Localized Fibre Sets construction uses the card fib G eq card pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AdjoinIntegralOfNonempty.lean#L107-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AdjoinIntegralOfNonempty.lean#L107-L185

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinIntegralOfNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.card_fibG_eq_card_pi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsLattice K Λ') (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hs1 : ∀ 𝔭 ∉ s, fibSet S L 𝔭.1 Λ' = {locF 𝔭.1 (S.adjoin Λ')}) :
    Nat.card (fibG S L Λ') = Nat.card (∀ 𝔭 : s, fibSet S L 𝔭.1.1 Λ') := by sorry
