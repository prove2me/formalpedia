-- Prove2me | solution 1 for mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:38:42.05038+00:00
-- url     : https://prove2.me/submissions/a39132d3-2d2d-47be-abee-3c6faeca3e2d

import Mathlib.Tactic
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_little_endian_MM_power_flatten
import Definitions.Def_mme_dwz_central_power_word_coordinates
import Theorems.Thm_mme_little_endian_MM_kronPow_tensor
import Theorems.Thm_mme_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
import Theorems.Thm_mme_basisZAllowedSubtensor_restrict_MM_first_of_exact_router

open MME PiTensorProduct TensorProduct Module
open MME.TensorObj MME.DWZComponentRestriction MME.DWZFineChannel

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace MME.DWZBalancedRectangularPower

private theorem kronPowModeMap_maps_tensor
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (f : ∀ i : Fin d, T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t) : ∀ n : ℕ,
    PiTensorProduct.map (fun i ↦ kronPowModeMap i (f i) n)
        (T.kronPow n).t = (S.kronPow n).t
  | 0 => by
      change PiTensorProduct.map (fun _ ↦ LinearMap.id)
          (TensorObj.oneObj (K := K) (d := d)).t =
        (TensorObj.oneObj (K := K) (d := d)).t
      simp
  | n + 1 => by
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map (f i)
            (kronPowModeMap i (f i) n))
          (interchange T.t (T.kronPow n).t) =
        interchange S.t (S.kronPow n).t
      rw [TensorObj.TypeGrading.kronMap_interchange, hf]
      rw [kronPowModeMap_maps_tensor f hf n]

private theorem littleEndianWordIndex_succ
    (P r : ℕ) (w : Fin (r + 1) → Fin P) :
    finProdFinEquiv
        (littleEndianWordIndex P r (fun i ↦ w i.succ), w 0) =
      littleEndianWordIndex P (r + 1) w := by
  apply Fin.ext
  simp [littleEndianWordIndex, finFunctionFinEquiv_apply,
    Fin.sum_univ_succ, pow_succ, finProdFinEquiv, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm]

private noncomputable def powerCoordinate
    {I : Type u} {P n : ℕ} (coord : I ↪ Fin P)
    (w : PowIndex I n) : Fin (P ^ n) :=
  littleEndianWordIndex P n (fun r ↦ coord (PowIndex.get n w r))

private theorem powerCoordinate_injective
    {I : Type u} {P n : ℕ} (coord : I ↪ Fin P) :
    Function.Injective (powerCoordinate coord : PowIndex I n → Fin (P ^ n)) := by
  intro w v h
  have hfun :
      (fun r ↦ coord (PowIndex.get n w r)) =
        (fun r ↦ coord (PowIndex.get n v r)) :=
    (littleEndianWordIndex P n).injective h
  apply (PowIndex.equivFun I n).injective
  funext r
  exact coord.injective (congrFun hfun r)

private noncomputable def powerCoordinateEmbedding
    {I : Type u} {P n : ℕ} (coord : I ↪ Fin P) :
    PowIndex I n ↪ Fin (P ^ n) :=
  ⟨powerCoordinate coord, powerCoordinate_injective coord⟩

/-! Normalize the two recursively singleton dimensions produced by the
little-endian MM flattening. -/

private noncomputable instance unitPowerUnique (n : ℕ) :
    Unique (Fin (1 ^ n)) where
  default := unitWordIndex n
  uniq x := by
    apply Fin.ext
    have hx : x.val < 1 := by simpa only [one_pow] using x.isLt
    have hu : (unitWordIndex n).val < 1 := by
      simpa only [one_pow] using (unitWordIndex n).isLt
    omega

private theorem funLeft_single_of_injective
    (K : Type u) [Field K] {A B : Type*}
    [DecidableEq A] [DecidableEq B]
    (f : B → A) (hf : Function.Injective f) (b : B) :
    LinearMap.funLeft K K f (Pi.single (f b) 1) =
      (Pi.single b 1 : B → K) := by
  classical
  funext x
  simp only [LinearMap.funLeft_apply, Pi.single_apply, hf.eq_iff]

private noncomputable def normalizeOneOnePower
    (K : Type u) [Field K] (P n : ℕ) :
    ∀ s : Fin 3,
      (MMObj K (1 ^ n) (1 ^ n) (P ^ n)).V s →ₗ[K]
        (MMObj K 1 1 (P ^ n)).V s
  | ⟨0, _⟩ => LinearMap.funLeft K K
      (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex n, unitWordIndex n))
  | ⟨1, _⟩ => LinearMap.funLeft K K
      (fun ab : Fin 1 × Fin (P ^ n) ↦ (unitWordIndex n, ab.2))
  | ⟨2, _⟩ => LinearMap.funLeft K K
      (fun ab : Fin (P ^ n) × Fin 1 ↦ (ab.1, unitWordIndex n))

private noncomputable def normalizeFirstPower
    (K : Type u) [Field K] (P n : ℕ) :
    ∀ s : Fin 3,
      (MMObj K (P ^ n) (1 ^ n) (1 ^ n)).V s →ₗ[K]
        (MMObj K (P ^ n) 1 1).V s
  | ⟨0, _⟩ => LinearMap.funLeft K K
      (fun ab : Fin (P ^ n) × Fin 1 ↦ (ab.1, unitWordIndex n))
  | ⟨1, _⟩ => LinearMap.funLeft K K
      (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex n, unitWordIndex n))
  | ⟨2, _⟩ => LinearMap.funLeft K K
      (fun ab : Fin 1 × Fin (P ^ n) ↦ (unitWordIndex n, ab.2))

private noncomputable def oneOneRawPure
    (K : Type u) [Field K] (P n : ℕ) (k : Fin (P ^ n)) :
    PiTensorProduct K (MMSpace K (1 ^ n) (1 ^ n) (P ^ n)) :=
  tprod K (fun s : Fin 3 ↦ match s with
    | ⟨0, _⟩ => (Pi.single (unitWordIndex n, unitWordIndex n) 1 :
        Fin (1 ^ n) × Fin (1 ^ n) → K)
    | ⟨1, _⟩ => (Pi.single (unitWordIndex n, k) 1 :
        Fin (1 ^ n) × Fin (P ^ n) → K)
    | ⟨2, _⟩ => (Pi.single (k, unitWordIndex n) 1 :
        Fin (P ^ n) × Fin (1 ^ n) → K))

private noncomputable def firstRawPure
    (K : Type u) [Field K] (P n : ℕ) (k : Fin (P ^ n)) :
    PiTensorProduct K (MMSpace K (P ^ n) (1 ^ n) (1 ^ n)) :=
  tprod K (fun s : Fin 3 ↦ match s with
    | ⟨0, _⟩ => (Pi.single (k, unitWordIndex n) 1 :
        Fin (P ^ n) × Fin (1 ^ n) → K)
    | ⟨1, _⟩ => (Pi.single (unitWordIndex n, unitWordIndex n) 1 :
        Fin (1 ^ n) × Fin (1 ^ n) → K)
    | ⟨2, _⟩ => (Pi.single (unitWordIndex n, k) 1 :
        Fin (1 ^ n) × Fin (P ^ n) → K))

private noncomputable def oneOneTargetPure
    (K : Type u) [Field K] (Q : ℕ) (k : Fin Q) :
    PiTensorProduct K (MMSpace K 1 1 Q) :=
  tprod K (fun s : Fin 3 ↦ match s with
    | ⟨0, _⟩ => (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 :
        Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin Q → K)
    | ⟨2, _⟩ => (Pi.single (k, (0 : Fin 1)) 1 : Fin Q × Fin 1 → K))

private noncomputable def firstTargetPure
    (K : Type u) [Field K] (Q : ℕ) (k : Fin Q) :
    PiTensorProduct K (MMSpace K Q 1 1) :=
  tprod K (fun s : Fin 3 ↦ match s with
    | ⟨0, _⟩ => (Pi.single (k, (0 : Fin 1)) 1 : Fin Q × Fin 1 → K)
    | ⟨1, _⟩ => (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 :
        Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin Q → K))

private theorem normalizeOneOnePower_selected
    (K : Type u) [Field K] (P n : ℕ) (k : Fin (P ^ n)) (s : Fin 3) :
    normalizeOneOnePower K P n s
        (match s with
        | ⟨0, _⟩ => (Pi.single (unitWordIndex n, unitWordIndex n) 1 :
            Fin (1 ^ n) × Fin (1 ^ n) → K)
        | ⟨1, _⟩ => (Pi.single (unitWordIndex n, k) 1 :
            Fin (1 ^ n) × Fin (P ^ n) → K)
        | ⟨2, _⟩ => (Pi.single (k, unitWordIndex n) 1 :
            Fin (P ^ n) × Fin (1 ^ n) → K)) =
      (match s with
      | ⟨0, _⟩ => (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 :
          Fin 1 × Fin 1 → K)
      | ⟨1, _⟩ => (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (P ^ n) → K)
      | ⟨2, _⟩ => (Pi.single (k, (0 : Fin 1)) 1 : Fin (P ^ n) × Fin 1 → K)) := by
  fin_cases s
  · exact funLeft_single_of_injective K
      (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex n, unitWordIndex n))
      (fun _ _ _ ↦ Subsingleton.elim _ _) ((0 : Fin 1), (0 : Fin 1))
  · exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin (P ^ n) ↦ (unitWordIndex n, ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact congrArg
            (fun x : Fin (1 ^ n) × Fin (P ^ n) ↦ x.2) h)
      ((0 : Fin 1), k)
  · exact funLeft_single_of_injective K
      (fun ab : Fin (P ^ n) × Fin 1 ↦ (ab.1, unitWordIndex n))
      (by
        intro a b h
        apply Prod.ext
        · exact congrArg
            (fun x : Fin (P ^ n) × Fin (1 ^ n) ↦ x.1) h
        · exact Subsingleton.elim _ _)
      (k, (0 : Fin 1))

private theorem normalizeFirstPower_selected
    (K : Type u) [Field K] (P n : ℕ) (k : Fin (P ^ n)) (s : Fin 3) :
    normalizeFirstPower K P n s
        (match s with
        | ⟨0, _⟩ => (Pi.single (k, unitWordIndex n) 1 :
            Fin (P ^ n) × Fin (1 ^ n) → K)
        | ⟨1, _⟩ => (Pi.single (unitWordIndex n, unitWordIndex n) 1 :
            Fin (1 ^ n) × Fin (1 ^ n) → K)
        | ⟨2, _⟩ => (Pi.single (unitWordIndex n, k) 1 :
            Fin (1 ^ n) × Fin (P ^ n) → K)) =
      (match s with
      | ⟨0, _⟩ => (Pi.single (k, (0 : Fin 1)) 1 : Fin (P ^ n) × Fin 1 → K)
      | ⟨1, _⟩ => (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 :
          Fin 1 × Fin 1 → K)
      | ⟨2, _⟩ => (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (P ^ n) → K)) := by
  fin_cases s
  · exact funLeft_single_of_injective K
      (fun ab : Fin (P ^ n) × Fin 1 ↦ (ab.1, unitWordIndex n))
      (by
        intro a b h
        apply Prod.ext
        · exact congrArg
            (fun x : Fin (P ^ n) × Fin (1 ^ n) ↦ x.1) h
        · exact Subsingleton.elim _ _)
      (k, (0 : Fin 1))
  · exact funLeft_single_of_injective K
      (fun _ : Fin 1 × Fin 1 ↦ (unitWordIndex n, unitWordIndex n))
      (fun _ _ _ ↦ Subsingleton.elim _ _) ((0 : Fin 1), (0 : Fin 1))
  · exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin (P ^ n) ↦ (unitWordIndex n, ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact congrArg
            (fun x : Fin (1 ^ n) × Fin (P ^ n) ↦ x.2) h)
      ((0 : Fin 1), k)

private theorem normalizeOneOnePower_map_pure
    (K : Type u) [Field K] (P n : ℕ) (k : Fin (P ^ n)) :
    PiTensorProduct.map (normalizeOneOnePower K P n)
        (oneOneRawPure K P n k) = oneOneTargetPure K (P ^ n) k := by
  unfold oneOneRawPure oneOneTargetPure
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  exact normalizeOneOnePower_selected K P n k s

private theorem normalizeFirstPower_map_pure
    (K : Type u) [Field K] (P n : ℕ) (k : Fin (P ^ n)) :
    PiTensorProduct.map (normalizeFirstPower K P n)
        (firstRawPure K P n k) = firstTargetPure K (P ^ n) k := by
  unfold firstRawPure firstTargetPure
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  exact normalizeFirstPower_selected K P n k s

private theorem normalizeOneOnePower_maps_tensor
    (K : Type u) [Field K] (P n : ℕ) :
    PiTensorProduct.map (normalizeOneOnePower K P n)
        (MMObj K (1 ^ n) (1 ^ n) (P ^ n)).t =
      (MMObj K 1 1 (P ^ n)).t := by
  have hraw : (MMObj K (1 ^ n) (1 ^ n) (P ^ n)).t =
      ∑ k : Fin (P ^ n), oneOneRawPure K P n k := by
    change MMTensor K (1 ^ n) (1 ^ n) (P ^ n) = _
    simp only [MMTensor, Finset.univ_unique, Finset.sum_singleton]
    rfl
  have htarget : (MMObj K 1 1 (P ^ n)).t =
      ∑ k : Fin (P ^ n), oneOneTargetPure K (P ^ n) k := by
    change MMTensor K 1 1 (P ^ n) = _
    simp only [MMTensor, Fin.sum_univ_one]
    rfl
  rw [hraw, htarget]
  refine (map_sum (PiTensorProduct.map (normalizeOneOnePower K P n))
    (fun k : Fin (P ^ n) ↦ oneOneRawPure K P n k) Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro k _
  exact normalizeOneOnePower_map_pure K P n k

private theorem normalizeFirstPower_maps_tensor
    (K : Type u) [Field K] (P n : ℕ) :
    PiTensorProduct.map (normalizeFirstPower K P n)
        (MMObj K (P ^ n) (1 ^ n) (1 ^ n)).t =
      (MMObj K (P ^ n) 1 1).t := by
  have hraw : (MMObj K (P ^ n) (1 ^ n) (1 ^ n)).t =
      ∑ k : Fin (P ^ n), firstRawPure K P n k := by
    change MMTensor K (P ^ n) (1 ^ n) (1 ^ n) = _
    simp only [MMTensor, Finset.univ_unique, Finset.sum_singleton]
    rfl
  have htarget : (MMObj K (P ^ n) 1 1).t =
      ∑ k : Fin (P ^ n), firstTargetPure K (P ^ n) k := by
    change MMTensor K (P ^ n) 1 1 = _
    simp only [MMTensor, Fin.sum_univ_one]
    rfl
  rw [hraw, htarget]
  refine (map_sum (PiTensorProduct.map (normalizeFirstPower K P n))
    (fun k : Fin (P ^ n) ↦ firstRawPure K P n k) Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro k _
  exact normalizeFirstPower_map_pure K P n k

private noncomputable def oneOneZPowerVec
    (K : Type u) [Field K] {I : Type u} (P : ℕ)
    (coord : I ↪ Fin P) :
    ∀ n : ℕ, PowIndex I n → ((MMObj K 1 1 P).kronPow n).V 2
  | 0, _ => (1 : K)
  | n + 1, w =>
      (Pi.single (coord w.1, (0 : Fin 1)) 1 : Fin P × Fin 1 → K) ⊗ₜ[K]
        oneOneZPowerVec K P coord n w.2

private noncomputable def firstZPowerVec
    (K : Type u) [Field K] {I : Type u} (P : ℕ)
    (coord : I ↪ Fin P) :
    ∀ n : ℕ, PowIndex I n → ((MMObj K P 1 1).kronPow n).V 2
  | 0, _ => (1 : K)
  | n + 1, w =>
      (Pi.single ((0 : Fin 1), coord w.1) 1 : Fin 1 × Fin P → K) ⊗ₜ[K]
        firstZPowerVec K P coord n w.2

private theorem kronPowModeMap_basis_oneOne
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} (bZ : Basis I K (T.V 2)) {P : ℕ}
    (coord : I ↪ Fin P)
    (routerZ : T.V 2 →ₗ[K] (MMObj K 1 1 P).V 2)
    (hrouterZ : ∀ i,
      routerZ (bZ i) =
        (Pi.single (coord i, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)) :
    ∀ (n : ℕ) (w : PowIndex I n),
      kronPowModeMap 2 routerZ n (kronPowModeBasis T 2 bZ n w) =
        oneOneZPowerVec K P coord n w
  | 0, w => by
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      change LinearMap.id
          ((Basis.singleton (PowIndex I 0) K) PUnit.unit) = (1 : K)
      simp
      try rfl
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      change (TensorProduct.map routerZ (kronPowModeMap 2 routerZ n))
          ((Module.Basis.tensorProduct bZ
            (kronPowModeBasis T 2 bZ n)) (a, tail)) = _
      rw [Module.Basis.tensorProduct_apply, TensorProduct.map_tmul,
        hrouterZ, kronPowModeMap_basis_oneOne bZ coord routerZ hrouterZ n tail]
      rfl

private theorem kronPowModeMap_basis_first
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} (bZ : Basis I K (T.V 2)) {P : ℕ}
    (coord : I ↪ Fin P)
    (routerZ : T.V 2 →ₗ[K] (MMObj K P 1 1).V 2)
    (hrouterZ : ∀ i,
      routerZ (bZ i) =
        (Pi.single ((0 : Fin 1), coord i) 1 : Fin 1 × Fin P → K)) :
    ∀ (n : ℕ) (w : PowIndex I n),
      kronPowModeMap 2 routerZ n (kronPowModeBasis T 2 bZ n w) =
        firstZPowerVec K P coord n w
  | 0, w => by
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      change LinearMap.id
          ((Basis.singleton (PowIndex I 0) K) PUnit.unit) = (1 : K)
      simp
      try rfl
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      change (TensorProduct.map routerZ (kronPowModeMap 2 routerZ n))
          ((Module.Basis.tensorProduct bZ
            (kronPowModeBasis T 2 bZ n)) (a, tail)) = _
      rw [Module.Basis.tensorProduct_apply, TensorProduct.map_tmul,
        hrouterZ, kronPowModeMap_basis_first bZ coord routerZ hrouterZ n tail]
      rfl

private theorem littleEndian_oneOneZPowerVec
    (K : Type u) [Field K] {I : Type u} (P : ℕ)
    (coord : I ↪ Fin P) : ∀ (n : ℕ) (w : PowIndex I n),
    littleEndianPowerMaps K 1 1 P n 2
        (oneOneZPowerVec K P coord n w) =
      (Pi.single (powerCoordinate coord w, unitWordIndex n) 1 :
        Fin (P ^ n) × Fin (1 ^ n) → K)
  | 0, w => by
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      change singletonPairMap K (1 : K) =
        (Pi.single (powerCoordinate (n := 0) coord PUnit.unit,
          unitWordIndex 0) 1 :
          Fin (P ^ 0) × Fin (1 ^ 0) → K)
      funext ab
      rw [show ab =
        (powerCoordinate (n := 0) coord PUnit.unit, unitWordIndex 0)
          from Subsingleton.elim _ _]
      simp [singletonPairMap]
      symm
      exact Pi.single_eq_same _ _
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      simp only [oneOneZPowerVec, littleEndianPowerMaps]
      change littleEndianKronEquiv K P 1 (P ^ n) (1 ^ n)
          ((TensorProduct.map LinearMap.id
            (littleEndianPowerMaps K 1 1 P n 2))
            ((Pi.single (coord a, (0 : Fin 1)) 1 : Fin P × Fin 1 → K) ⊗ₜ[K]
              oneOneZPowerVec K P coord n tail)) = _
      rw [TensorProduct.map_tmul, LinearMap.id_apply,
        littleEndian_oneOneZPowerVec K P coord n tail]
      calc
        _ = Pi.single
            (finProdFinEquiv (powerCoordinate coord tail, coord a),
              finProdFinEquiv (unitWordIndex n, (0 : Fin 1))) 1 :=
          littleEndianKronEquiv_single K (coord a) (0 : Fin 1)
            (powerCoordinate coord tail) (unitWordIndex n)
        _ = _ := by
          congr 2
          · exact littleEndianWordIndex_succ P n
              (fun r ↦ coord (PowIndex.get (n + 1) (a, tail) r))
          · exact littleEndianWordIndex_succ 1 n
              (fun _ ↦ (0 : Fin 1))

private theorem littleEndian_firstZPowerVec
    (K : Type u) [Field K] {I : Type u} (P : ℕ)
    (coord : I ↪ Fin P) : ∀ (n : ℕ) (w : PowIndex I n),
    littleEndianPowerMaps K P 1 1 n 2
        (firstZPowerVec K P coord n w) =
      (Pi.single (unitWordIndex n, powerCoordinate coord w) 1 :
        Fin (1 ^ n) × Fin (P ^ n) → K)
  | 0, w => by
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      change singletonPairMap K (1 : K) =
        (Pi.single (unitWordIndex 0,
          powerCoordinate (n := 0) coord PUnit.unit) 1 :
          Fin (1 ^ 0) × Fin (P ^ 0) → K)
      funext ab
      rw [show ab =
        (unitWordIndex 0, powerCoordinate (n := 0) coord PUnit.unit)
          from Subsingleton.elim _ _]
      simp [singletonPairMap]
      symm
      exact Pi.single_eq_same _ _
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      simp only [firstZPowerVec, littleEndianPowerMaps]
      change littleEndianKronEquiv K 1 P (1 ^ n) (P ^ n)
          ((TensorProduct.map LinearMap.id
            (littleEndianPowerMaps K P 1 1 n 2))
            ((Pi.single ((0 : Fin 1), coord a) 1 : Fin 1 × Fin P → K) ⊗ₜ[K]
              firstZPowerVec K P coord n tail)) = _
      rw [TensorProduct.map_tmul, LinearMap.id_apply,
        littleEndian_firstZPowerVec K P coord n tail]
      calc
        _ = Pi.single
            (finProdFinEquiv (unitWordIndex n, (0 : Fin 1)),
              finProdFinEquiv (powerCoordinate coord tail, coord a)) 1 :=
          littleEndianKronEquiv_single K (0 : Fin 1) (coord a)
            (unitWordIndex n) (powerCoordinate coord tail)
        _ = _ := by
          congr 2
          · exact littleEndianWordIndex_succ 1 n
              (fun _ ↦ (0 : Fin 1))
          · exact littleEndianWordIndex_succ P n
              (fun r ↦ coord (PowIndex.get (n + 1) (a, tail) r))

/-- An exact one-letter router to `MM(1,1,P)` lifts through a Kronecker
power and then descends through an arbitrary literal Z-word selection. -/
theorem powerAllowedSubtensor_restrict_oneOne
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (n : ℕ)
    (allowed : PowIndex I n → Prop) [DecidablePred allowed]
    {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K 1 1 P).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K 1 1 P).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single (coord i, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)) :
    TensorObj.Restrict
      (MMObj K 1 1 (Nat.card {w : PowIndex I n // allowed w}))
      ((T.kronPow n).basisZAllowedSubtensor
        (kronPowModeBasis T 2 bZ n) allowed) := by
  let sourcePower : ∀ s,
      (T.kronPow n).V s →ₗ[K] ((MMObj K 1 1 P).kronPow n).V s :=
    fun s ↦ kronPowModeMap s (router s) n
  let flatRaw : ∀ s, (T.kronPow n).V s →ₗ[K]
      (MMObj K (1 ^ n) (1 ^ n) (P ^ n)).V s := fun s ↦
    (littleEndianPowerMaps K 1 1 P n s).comp (sourcePower s)
  let flat : ∀ s, (T.kronPow n).V s →ₗ[K]
      (MMObj K 1 1 (P ^ n)).V s := fun s ↦
    (normalizeOneOnePower K P n s).comp (flatRaw s)
  have hsource : PiTensorProduct.map sourcePower (T.kronPow n).t =
      ((MMObj K 1 1 P).kronPow n).t :=
    kronPowModeMap_maps_tensor router hrouter n
  have hflat : PiTensorProduct.map flat (T.kronPow n).t =
      (MMObj K 1 1 (P ^ n)).t := by
    have hraw : PiTensorProduct.map flatRaw (T.kronPow n).t =
        (MMObj K (1 ^ n) (1 ^ n) (P ^ n)).t := by
      change PiTensorProduct.map
          (fun s ↦ (littleEndianPowerMaps K 1 1 P n s) ∘ₗ sourcePower s)
            (T.kronPow n).t =
          (MMObj K (1 ^ n) (1 ^ n) (P ^ n)).t
      rw [PiTensorProduct.map_comp]
      simp only [LinearMap.comp_apply]
      rw [hsource, mme_little_endian_MM_kronPow_tensor]
    change PiTensorProduct.map
        (fun s ↦ (normalizeOneOnePower K P n s) ∘ₗ flatRaw s)
          (T.kronPow n).t = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [hraw, normalizeOneOnePower_maps_tensor]
  have hflatZ : ∀ w,
      flat 2 (kronPowModeBasis T 2 bZ n w) =
        (Pi.single (powerCoordinateEmbedding coord w, (0 : Fin 1)) 1 :
          Fin (P ^ n) × Fin 1 → K) := by
    intro w
    have hraw := littleEndian_oneOneZPowerVec K P coord n w
    rw [← kronPowModeMap_basis_oneOne bZ coord (router 2) hrouterZ n w]
      at hraw
    have hraw' :
        flatRaw 2 (kronPowModeBasis T 2 bZ n w) =
          (Pi.single (powerCoordinate coord w, unitWordIndex n) 1 :
            Fin (P ^ n) × Fin (1 ^ n) → K) := by
      simpa only [flatRaw, sourcePower, LinearMap.comp_apply] using hraw
    simp only [flat, LinearMap.comp_apply, hraw']
    exact normalizeOneOnePower_selected K P n (powerCoordinate coord w) 2
  exact mme_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
    (kronPowModeBasis T 2 bZ n) allowed (powerCoordinateEmbedding coord)
    flat hflat hflatZ

/-- Mode-rotated companion for an exact one-letter router to `MM(P,1,1)`. -/
theorem powerAllowedSubtensor_restrict_first
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (n : ℕ)
    (allowed : PowIndex I n → Prop) [DecidablePred allowed]
    {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K P 1 1).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K P 1 1).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single ((0 : Fin 1), coord i) 1 : Fin 1 × Fin P → K)) :
    TensorObj.Restrict
      (MMObj K (Nat.card {w : PowIndex I n // allowed w}) 1 1)
      ((T.kronPow n).basisZAllowedSubtensor
        (kronPowModeBasis T 2 bZ n) allowed) := by
  let sourcePower : ∀ s,
      (T.kronPow n).V s →ₗ[K] ((MMObj K P 1 1).kronPow n).V s :=
    fun s ↦ kronPowModeMap s (router s) n
  let flatRaw : ∀ s, (T.kronPow n).V s →ₗ[K]
      (MMObj K (P ^ n) (1 ^ n) (1 ^ n)).V s := fun s ↦
    (littleEndianPowerMaps K P 1 1 n s).comp (sourcePower s)
  let flat : ∀ s, (T.kronPow n).V s →ₗ[K]
      (MMObj K (P ^ n) 1 1).V s := fun s ↦
    (normalizeFirstPower K P n s).comp (flatRaw s)
  have hsource : PiTensorProduct.map sourcePower (T.kronPow n).t =
      ((MMObj K P 1 1).kronPow n).t :=
    kronPowModeMap_maps_tensor router hrouter n
  have hflat : PiTensorProduct.map flat (T.kronPow n).t =
      (MMObj K (P ^ n) 1 1).t := by
    have hraw : PiTensorProduct.map flatRaw (T.kronPow n).t =
        (MMObj K (P ^ n) (1 ^ n) (1 ^ n)).t := by
      change PiTensorProduct.map
          (fun s ↦ (littleEndianPowerMaps K P 1 1 n s) ∘ₗ sourcePower s)
            (T.kronPow n).t =
          (MMObj K (P ^ n) (1 ^ n) (1 ^ n)).t
      rw [PiTensorProduct.map_comp]
      simp only [LinearMap.comp_apply]
      rw [hsource, mme_little_endian_MM_kronPow_tensor]
    change PiTensorProduct.map
        (fun s ↦ (normalizeFirstPower K P n s) ∘ₗ flatRaw s)
          (T.kronPow n).t = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [hraw, normalizeFirstPower_maps_tensor]
  have hflatZ : ∀ w,
      flat 2 (kronPowModeBasis T 2 bZ n w) =
        (Pi.single ((0 : Fin 1), powerCoordinateEmbedding coord w) 1 :
          Fin 1 × Fin (P ^ n) → K) := by
    intro w
    have hraw := littleEndian_firstZPowerVec K P coord n w
    rw [← kronPowModeMap_basis_first bZ coord (router 2) hrouterZ n w]
      at hraw
    have hraw' :
        flatRaw 2 (kronPowModeBasis T 2 bZ n w) =
          (Pi.single (unitWordIndex n, powerCoordinate coord w) 1 :
            Fin (1 ^ n) × Fin (P ^ n) → K) := by
      simpa only [flatRaw, sourcePower, LinearMap.comp_apply] using hraw
    simp only [flat, LinearMap.comp_apply, hraw']
    exact normalizeFirstPower_selected K P n (powerCoordinate coord w) 2
  exact mme_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
    (kronPowModeBasis T 2 bZ n) allowed (powerCoordinateEmbedding coord)
    flat hflat hflatZ

end MME.DWZBalancedRectangularPower

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (n : ℕ)
    (allowed : MME.DWZComponentRestriction.PowIndex I n → Prop)
    [DecidablePred allowed]
    {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K 1 1 P).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K 1 1 P).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single (coord i, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)) :
    TensorObj.Restrict
      (MMObj K 1 1 (Nat.card
        {w : MME.DWZComponentRestriction.PowIndex I n // allowed w}))
      ((T.kronPow n).basisZAllowedSubtensor
        (MME.DWZComponentRestriction.kronPowModeBasis T 2 bZ n) allowed) := by
  exact MME.DWZBalancedRectangularPower.powerAllowedSubtensor_restrict_oneOne
    bZ n allowed coord router hrouter hrouterZ
