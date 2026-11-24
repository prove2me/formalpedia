-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_length_quot_map_positionMap
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.length_quot_map_positionMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:03.045489+00:00
-- url     : https://prove2.me/theorems/2a95cc8b-7e21-46c6-a37e-7c9d0d1afa29
-- title:
--   Local Lattice Bases: length quot map position Map
-- statement:
--   The Local Lattice Bases construction uses the length quot map position Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L196-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L196-L206

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
variable {K : Type*} [Field K]

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.length_quot_map_positionMap {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ))
    (O : Subring K) (A₀ B₀ : Submodule O (MvPolynomial σ K)) :
    Module.length O (((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
          ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)) ⧸
        ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => B₀).map ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).comap
          ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
            ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) • Module.length O (A₀ ⧸ B₀.comap A₀.subtype) := by sorry
