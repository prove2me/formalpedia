-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_levelsQDesc
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.levelsQDesc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:57:20.937487+00:00
-- url     : https://prove2.me/theorems/8dda7463-1e59-4278-9738-f1f917c44c33
-- title:
--   Etale Weight Gaps: levels QDesc
-- statement:
--   The Etale Weight Gaps construction uses the levels QDesc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LevelsQDesc.lean#L9-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LevelsQDesc.lean#L9-L83

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LevelsQDesc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot Formalism.MainNotions.Gaps.T0

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.levelsQDesc (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ)
    (hep : ∀ z, 1 ≤ ep z) (hT : 1 ≤ T) (hc' : 0 ≤ c') (hv : ∀ z, 0 ≤ v z) (hν : ∀ z, ν z ≤ νs + c' * v z)
    (O O' K K' V V₁ W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] [AddCommGroup W] [Module O' W]
    (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j)
    (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (M Θ Mgg : Submodule O V) (N₁ Z Zm N' : Submodule O' V₁) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O' W) (ρ : ↥N' →ₗ[O'] W)
    (hM : Formalism.LatticeIndexTer.IsLat O K V M) (hΘ : Formalism.LatticeIndexTer.IsLat O K V Θ)
    (h1 : N₁ ⊔ Z ≤ Submodule.span O' (j '' (Θ : Set V))) (h2 : ∀ i, th i ∈ M) (h3 : ∀ i, th i ∈ Θ)
    (h4 : Mgg ≤ M)
    (h5 : ∀ x ∈ Mgg, j x ∈ Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁))
    (h6 : Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞))
    (h8 : (Submodule.span O' (j '' (M : Set V))).map
        ((algebraMap O O' ϖ ^ e) • (LinearMap.id : V₁ →ₗ[O'] V₁)) ⊓
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' ≤ N')
    (h9 : N₁ ≤ N') (h10 : Z ≤ Zm) (h11 : Zm ≤ N') (h12 : ∀ x, ρ x ∈ AA')
    (h13 : LinearMap.ker ρ = Zm.comap N'.subtype) (h14 : (N₁.comap N'.subtype).map ρ = N₁') (h15 : N₁' ≤ AA)
    (h16 : AA ≤ AA')
    (h17 : Module.length O' (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤)
    (hcase : ((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ))
    (hA : Module.length O' (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℕ∞))
    (hN : Module.length O' (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞))
    (V' : Submodule K V) :
    (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
      (e : ℝ) * (finrank K V' : ℝ) +
          (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
          ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ) := by sorry
