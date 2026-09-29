-- Prove2me | solution 1 for mme_dwz_central_022_202_restricted_source_words_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:52:53.403366+00:00
-- url     : https://prove2.me/submissions/14d47469-4681-4721-a90d-3d8d2beff1be

import Definitions.Def_mme_dwz_central_restricted_word_projectors
import Theorems.Thm_mme_dwz_cw_square_central_022_202_restricted_word_power_router
import Theorems.Thm_mme_little_endian_MM_kronPow_tensor
import Theorems.Thm_mme_dwz_central_022_202_power_word_coordinates

open PiTensorProduct
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem solution
    (K : Type u) [Field K] (q m L G : ℕ) :
    (exists maps022 : ∀ s : Fin 3,
        ((Central022Block K q).kronPow m).V s →ₗ[K]
          (MMObj K 1 1
            (Nat.card (CentralRestricted022Word q m L G))).V s,
      PiTensorProduct.map maps022 ((Central022Block K q).kronPow m).t =
          (MMObj K 1 1
            (Nat.card (CentralRestricted022Word q m L G))).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps022 s
            (central022SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          restricted022TargetMMVec K
            (Nat.card (CentralRestricted022Word q m L G))
            (centralRestrictedWordEquivFin q m L G w) s) ∧
    (exists maps202 : ∀ s : Fin 3,
        ((Central202Block K q).kronPow m).V s →ₗ[K]
          (MMObj K
            (Nat.card (CentralRestricted022Word q m L G)) 1 1).V s,
      PiTensorProduct.map maps202 ((Central202Block K q).kronPow m).t =
          (MMObj K
            (Nat.card (CentralRestricted022Word q m L G)) 1 1).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps202 s
            (central202SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          restricted202TargetMMVec K
            (Nat.card (CentralRestricted022Word q m L G))
            (centralRestrictedWordEquivFin q m L G w) s) := by
  rcases
      mme_dwz_cw_square_central_022_202_restricted_word_power_router
        K q m L G with
    ⟨⟨source022, htensor022, hword022⟩,
      ⟨source202, htensor202, hword202⟩⟩
  obtain ⟨hcoordinate022, hcoordinate202⟩ :=
    mme_dwz_central_022_202_power_word_coordinates K q m
  let D := Nat.card (CentralRestricted022Word q m L G)
  let e : Fin D ↪ Fin ((q ^ 2 + 2) ^ m) :=
    centralRestrictedWordEmbedding q m L G
  refine ⟨⟨fun s ↦
      (central022RestrictedProjector (K := K) e s).comp
        ((littleEndianPowerMaps K 1 1 (q ^ 2 + 2) m s).comp
          (source022 s)), ?_, ?_⟩,
    ⟨fun s ↦
      (central202RestrictedProjector (K := K) e s).comp
        ((littleEndianPowerMaps K (q ^ 2 + 2) 1 1 m s).comp
          (source202 s)), ?_, ?_⟩⟩
  · change PiTensorProduct.map
        (fun s ↦
          (central022RestrictedProjector (K := K) e s) ∘ₗ
            ((littleEndianPowerMaps K 1 1 (q ^ 2 + 2) m s) ∘ₗ
              source022 s))
        ((Central022Block K q).kronPow m).t =
      (MMObj K 1 1 D).t
    rw [PiTensorProduct.map_comp, PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [htensor022, mme_little_endian_MM_kronPow_tensor,
      central022RestrictedProjector_maps_tensor]
  · intro w s
    simp only [LinearMap.comp_apply]
    rw [hword022 w s,
      hcoordinate022 (encodeCentralRestricted022Word w) s]
    have hindex :
        fineChannelWordIndex q m (encodeCentralRestricted022Word w) =
          e (centralRestrictedWordEquivFin q m L G w) := by
      simpa only [D, e, centralRestrictedWordCoordinate] using
        (centralRestrictedWordEmbedding_word w).symm
    rw [hindex]
    exact central022RestrictedProjector_selected e
      (centralRestrictedWordEquivFin q m L G w) s
  · change PiTensorProduct.map
        (fun s ↦
          (central202RestrictedProjector (K := K) e s) ∘ₗ
            ((littleEndianPowerMaps K (q ^ 2 + 2) 1 1 m s) ∘ₗ
              source202 s))
        ((Central202Block K q).kronPow m).t =
      (MMObj K D 1 1).t
    rw [PiTensorProduct.map_comp, PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [htensor202, mme_little_endian_MM_kronPow_tensor,
      central202RestrictedProjector_maps_tensor]
  · intro w s
    simp only [LinearMap.comp_apply]
    rw [hword202 w s,
      hcoordinate202 (encodeCentralRestricted022Word w) s]
    have hindex :
        fineChannelWordIndex q m (encodeCentralRestricted022Word w) =
          e (centralRestrictedWordEquivFin q m L G w) := by
      simpa only [D, e, centralRestrictedWordCoordinate] using
        (centralRestrictedWordEmbedding_word w).symm
    rw [hindex]
    exact central202RestrictedProjector_selected e
      (centralRestrictedWordEquivFin q m L G w) s
