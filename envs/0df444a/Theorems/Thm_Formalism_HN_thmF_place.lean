-- Prove2me | Theorems.Thm_Formalism_HN_thmF_place
-- name    : Formalism.HN.thmF_place
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:00.425+00:00
-- url     : https://prove2.me/theorems/c6c9ad21-ff9b-4f6c-84ee-d9c957654a3c
-- title:
--   HN: thm F place
-- statement:
--   The HN construction uses the thm F place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L35-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L35-L159

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.thmF_place {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (hLA : FrameLA1)
    (b' : Basis κ K W) (b : ∀ i, Basis (ι i) K (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (c : I → ℝ)
    (e η ε : ℝ) (Nt : ∀ i, Submodule (𝓞 K) (V i))
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det) (hc : ∀ i, 0 < c i)
    (hpos : 0 < ∑ i, Fintype.card (ι i))
    (hBall : ∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
    (hF2 : (∑ i, hs2 (frK (c i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hη : 0 ≤ η)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ))
    (hcor : (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) ≤ ε * ∑ i, (Fintype.card (ι i) : ℝ)) :
    (Fintype.card κ : ℝ) - rkK (⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))) ≤
      (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := by sorry
