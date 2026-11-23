-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrthogonalBases_sup_eq_top_of_mem_hcompl
-- name    : Formalism.HermitianLattices.Ext.L3.OrthogonalBases.sup_eq_top_of_mem_hcompl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:48.554801+00:00
-- url     : https://prove2.me/theorems/a847381d-4b1d-4f03-8558-c35c5ec41dda
-- title:
--   Orthogonal Bases: sup eq top of mem hcompl
-- statement:
--   The Orthogonal Bases construction uses the sup eq top of mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SupEqTopOfMemHcompl.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SupEqTopOfMemHcompl.lean#L13-L30

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SupEqTopOfMemHcompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.OrthogonalBases
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.OrthogonalBases.sup_eq_top_of_mem_hcompl (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {u : 𝓞 K} (hu : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    Ideal.span {u} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤ := by sorry
