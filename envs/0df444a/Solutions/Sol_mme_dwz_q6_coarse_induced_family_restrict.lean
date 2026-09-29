-- Prove2me | solution 1 for mme_dwz_q6_coarse_induced_family_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:43:48.785358+00:00
-- url     : https://prove2.me/submissions/e6afc231-d6f4-4811-b6e9-9de20cd66fc0

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks
import Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled121_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled211_restrict
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Mathlib.Tactic

open MME

universe u

/-! The two local lemmas below are tensor-functoriality only.  The mathematical
content of `solution` is that the fifteen concrete Table-2 constituents are
the restrictions supplied by the canonical five-grading, and that an induced
family can therefore be substituted into the standard graded-word zeroing. -/

private theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright

private theorem kronFin_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (N : ℕ) (X Y : Fin N → TensorObj K d),
      (∀ r, TensorObj.Restrict (X r) (Y r)) →
      TensorObj.Restrict (TensorObj.kronFin N X) (TensorObj.kronFin N Y) := by
  intro N
  induction N with
  | zero =>
      intro X Y _
      exact TensorObj.Restrict.refl _
  | succ N ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin N (fun r ↦ X r.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin N (fun r ↦ Y r.succ)))
      exact kron_restrict hd (h 0)
        (ih (fun r ↦ X r.succ) (fun r ↦ Y r.succ) (fun r ↦ h r.succ))

private theorem vec3_eq_cwSquareBlockType
    (I J L : Fin 5) :
    (fun i ↦ (![I, J, L] : Fin 3 → Fin 5) i) =
      cwSquareBlockType I J L := by
  funext i
  fin_cases i <;> rfl

open MME.DWZSquare

theorem solution
    {K : Type u} [Field K] {N k : ℕ}
    (component : Fin k → Fin N → Fin 15)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦
            (![shapeX (component (js i) r),
               shapeY (component (js i) r),
               shapeZ (component (js i) r)] : Fin 3 → Fin 5) i) ≠ 0) →
      ∃ j : Fin k, js = fun _ ↦ j) :
    let coarseComponent : Fin 15 → TensorObj K 3 :=
      ![MMObj K 1 1 1,
        MMObj K 1 1 1,
        MMObj K 1 1 1,
        MMObj K 1 1 12,
        MMObj K 1 1 12,
        MMObj K 12 1 1,
        MMObj K 1 12 1,
        MMObj K 12 1 1,
        MMObj K 1 12 1,
        MMObj K 1 1 38,
        MMObj K 38 1 1,
        MMObj K 1 38 1,
        coupledObj K 6,
        TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6),
        TensorObj.permObj cyclicPerm (coupledObj K 6)]
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        TensorObj.kronFin N (fun r ↦ coarseComponent (component j r))))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N) := by
  let G := cwSquareCanonicalGrading K 6
  let coarseComponent : Fin 15 → TensorObj K 3 :=
    ![MMObj K 1 1 1,
      MMObj K 1 1 1,
      MMObj K 1 1 1,
      MMObj K 1 1 12,
      MMObj K 1 1 12,
      MMObj K 12 1 1,
      MMObj K 1 12 1,
      MMObj K 12 1 1,
      MMObj K 1 12 1,
      MMObj K 1 1 38,
      MMObj K 38 1 1,
      MMObj K 1 38 1,
      coupledObj K 6,
      TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6),
      TensorObj.permObj cyclicPerm (coupledObj K 6)]
  let address : Fin k → Fin 3 → Fin N → Fin 5 := fun j i r ↦
    (![shapeX (component j r),
       shapeY (component j r),
       shapeZ (component j r)] : Fin 3 → Fin 5) i
  change TensorObj.Restrict
    (TensorObj.bigAdd (fun j ↦
      TensorObj.kronFin N (fun r ↦ coarseComponent (component j r))))
    ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N)

  rcases mme_CW_square_canonical_elementary_blocks (K := K) 6 with
    ⟨_, h004, h040, h400, h013, h031, h103, h301, h130, h310,
      h022, h202, h220⟩
  have hComponent : ∀ s : Fin 15,
      TensorObj.Restrict (coarseComponent s)
        (G.blockSubtensor
          (fun i ↦
            (![shapeX s, shapeY s, shapeZ s] : Fin 3 → Fin 5) i)) := by
    intro s
    fin_cases s
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h004
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h040
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h400
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h013
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h031
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h103
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h130
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h301
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h310
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h022
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h202
    · simpa [coarseComponent, G, shapeX, shapeY, shapeZ,
        vec3_eq_cwSquareBlockType] using h220
    · simp only [vec3_eq_cwSquareBlockType]
      exact mme_CW_square_canonical_coupled112_restrict (K := K) 6
    · simp only [vec3_eq_cwSquareBlockType]
      exact mme_CW_square_canonical_coupled121_restrict (K := K) 6
    · simp only [vec3_eq_cwSquareBlockType]
      exact mme_CW_square_canonical_coupled211_restrict (K := K) 6

  have hEach : ∀ j : Fin k,
      TensorObj.Restrict
        (TensorObj.kronFin N (fun r ↦ coarseComponent (component j r)))
        (gradedAddressBlock G (address j)) := by
    intro j
    apply kronFin_restrict (d := 3) (by omega)
    intro r
    simpa only [address, gradedAddressBlock] using hComponent (component j r)

  have hBig : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        TensorObj.kronFin N (fun r ↦ coarseComponent (component j r))))
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (address j))) :=
    mme_bigAdd_mono_restrict hEach
  have hZeroing : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (address j)))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N) := by
    apply mme_induced_graded_address_blocks_restrict G address
    intro js hnonzero
    apply hInduced js
    simpa only [address, G] using hnonzero
  exact TensorObj.Restrict.trans hBig hZeroing
