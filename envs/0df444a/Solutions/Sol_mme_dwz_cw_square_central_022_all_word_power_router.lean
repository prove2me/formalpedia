-- Prove2me | solution 1 for mme_dwz_cw_square_central_022_all_word_power_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:05:16.695281+00:00
-- url     : https://prove2.me/submissions/276d9011-5dfa-4f76-9699-ec745d0dd936

import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Theorems.Thm_mme_dwz_cw_square_central_022_202_source_router

open PiTensorProduct TensorProduct
open MME MME.DWZFineChannel

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

theorem solution
    (K : Type u) [Field K] (q n : ℕ) :
    ∃ maps : ∀ s : Fin 3,
        ((Central022Block K q).kronPow n).V s →ₗ[K]
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow n).V s,
      PiTensorProduct.map maps ((Central022Block K q).kronPow n).t =
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow n).t ∧
      ∀ (w : Fin n → Fine022Channel q) (s : Fin 3),
        maps s (central022SourceWordVec K q n w s) =
          central022MMWordVec K q n w s := by
  rcases mme_dwz_cw_square_central_022_202_source_router K q with
    ⟨⟨base, hbase, hletter⟩, _⟩
  have htensor : ∀ r : ℕ,
      PiTensorProduct.map (central022PowerMapsFrom K q base r)
          ((Central022Block K q).kronPow r).t =
        ((MMObj K 1 1 (q ^ 2 + 2)).kronPow r).t := by
    intro r
    induction r with
    | zero =>
        change PiTensorProduct.map (fun _ : Fin 3 => LinearMap.id)
            (PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))) =
          PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))
        rw [PiTensorProduct.map_tprod]
        rfl
    | succ r ih =>
        change PiTensorProduct.map
            (fun s => TensorProduct.map (base s)
              (central022PowerMapsFrom K q base r s))
            (interchange
              ((cwSquareCanonicalGrading K q).blockTensor
                (cwSquareBlockType 0 2 2))
              ((Central022Block K q).kronPow r).t) =
          interchange (MMTensor K 1 1 (q ^ 2 + 2))
            ((MMObj K 1 1 (q ^ 2 + 2)).kronPow r).t
        rw [TensorObj.TypeGrading.kronMap_interchange, hbase, ih]
        rfl
  have hword : ∀ (r : ℕ) (w : Fin r → Fine022Channel q)
      (s : Fin 3),
      central022PowerMapsFrom K q base r s
          (central022SourceWordVec K q r w s) =
        central022MMWordVec K q r w s := by
    intro r
    induction r with
    | zero =>
        intro w s
        rfl
    | succ r ih =>
        intro w s
        simp only [central022SourceWordVec, central022MMWordVec,
          central022PowerMapsFrom]
        calc
          _ = base s (central022SourceVec K q (w 0) s) ⊗ₜ[K]
                central022PowerMapsFrom K q base r s
                  (central022SourceWordVec K q r
                    (fun i => w i.succ) s) :=
            TensorProduct.map_tmul (base s)
              (central022PowerMapsFrom K q base r s)
              (central022SourceVec K q (w 0) s)
              (central022SourceWordVec K q r (fun i => w i.succ) s)
          _ = _ := by rw [central022SourceVec, hletter, ih]
  exact ⟨central022PowerMapsFrom K q base n, htensor n, hword n⟩
