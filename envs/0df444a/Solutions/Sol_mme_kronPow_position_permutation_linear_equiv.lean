-- Prove2me | solution 1 for mme_kronPow_position_permutation_linear_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:55:32.580361+00:00
-- url     : https://prove2.me/submissions/dcc34d54-a7df-4cf2-a061-838c4396d3da

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Mathlib.Algebra.BigOperators.Fin

open MME MME.TensorObj PiTensorProduct TensorProduct BigOperators Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

private theorem interchange_tprod_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  change (PiTensorProduct.lift interchangeOuter (tprod K v))
      (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_basis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (c : ∀ i, Basis (κ i) K (W i))
    (x : PiTensorProduct K V) (y : PiTensorProduct K W)
    (p : ∀ i, ι i) (q : ∀ i, κ i) :
    (Basis.piTensorProduct
        (fun i ↦ Module.Basis.tensorProduct (b i) (c i))).repr
        (interchange x y) (fun i ↦ (p i, q i)) =
      (Basis.piTensorProduct b).repr x p *
        (Basis.piTensorProduct c).repr y q := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod a' w =>
          simp [interchange_tprod_explicit, Finset.prod_mul_distrib]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply, mul_add, hy, hz]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply,
        add_mul, hx, hz]

private theorem piTensorProduct_basis_reindex_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (e : ∀ i, ι i ≃ κ i) :
    Basis.piTensorProduct (fun i ↦ (b i).reindex (e i)) =
      (Basis.piTensorProduct b).reindex (Equiv.piCongrRight e) := by
  ext w
  simp [Basis.piTensorProduct_apply,
    Module.Basis.reindex_apply]

private theorem basis_repr_equiv_self_explicit
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι : Type u} (B : Basis ι K V) (E : Equiv.Perm ι)
    (x : V) (w : ι) :
    B.repr (B.equiv B E x) w = B.repr x (E.symm w) := by
  have h := congrArg (fun f : ι →₀ K ↦ f (E.symm w))
    ((B.reindex E.symm).repr.apply_symm_apply (B.repr x))
  change
    (B.reindex E.symm).repr
        ((B.reindex E.symm).repr.symm (B.repr x)) (E.symm w) =
      B.repr x (E.symm w) at h
  rw [Module.Basis.repr_reindex_apply] at h
  simpa [Module.Basis.equiv, LinearEquiv.trans_apply] using h

@[simp]
private theorem kronPowModeWordBasis_succ_apply_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (w : Fin (n + 1) → ι) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K]
        kronPowModeWordBasis T i b n (fun r ↦ w r.succ) := by
  rw [kronPowModeWordBasis]
  calc
    _ = (Module.Basis.tensorProduct b
          (kronPowModeWordBasis T i b n))
        ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).symm w) :=
      Module.Basis.reindex_apply _ _ _
    _ = _ := by
      rw [Fin.consEquiv_symm_apply,
        Module.Basis.tensorProduct_apply]
      rfl

private noncomputable def kronPowTensorWordBasisExplicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) (n : ℕ) :
    Basis (∀ i, Fin n → ι i) K
      (PiTensorProduct K (fun i ↦ (T.kronPow n).V i)) :=
  Basis.piTensorProduct
    (fun i ↦ kronPowModeWordBasis T i (b i) n)

private theorem kronPowTensorWordBasis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (w : ∀ i, Fin n → ι i) :
    (kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t w =
      ∏ r : Fin n,
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i r) := by
  induction n with
  | zero =>
      change
        (Basis.piTensorProduct
          (fun i ↦ Basis.singleton (Fin 0 → ι i) K)).repr
            (tprod K (fun _ ↦ (1 : K))) w = 1
      rw [Basis.piTensorProduct_repr_tprod_apply]
      simp only [Module.Basis.singleton_repr, Finset.prod_const_one]
  | succ n ih =>
      change
        (Basis.piTensorProduct
          (fun i ↦
            (Module.Basis.tensorProduct (b i)
              (kronPowModeWordBasis T i (b i) n)).reindex
                (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι i)))).repr
          (interchange T.t (T.kronPow n).t) w = _
      rw [piTensorProduct_basis_reindex_explicit]
      rw [Module.Basis.repr_reindex_apply]
      rw [interchange_basis_repr_explicit]
      simp only [Equiv.piCongrRight_symm_apply,
        Pi.map_apply, Fin.consEquiv_symm_apply]
      change
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i 0) *
          (kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t
            (fun i r ↦ w i r.succ) = _
      rw [ih]
      rw [Fin.prod_univ_succ]

@[simp]
private theorem kronPowModePositionEquiv_basis_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (e : Equiv.Perm (Fin n))
    (w : Fin n → ι) :
    kronPowModePositionEquiv T i b n e
        (kronPowModeWordBasis T i b n w) =
      kronPowModeWordBasis T i b n (fun r ↦ w (e r)) := by
  exact Basis.equiv_apply _ _ _ _

private theorem kronPowModePositionEquiv_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (e : Equiv.Perm (Fin n))
    (x : (T.kronPow n).V i) (w : Fin n → ι) :
    (kronPowModeWordBasis T i b n).repr
        (kronPowModePositionEquiv T i b n e x) w =
      (kronPowModeWordBasis T i b n).repr x
        ((kronPowWordReindex e ι).symm w) := by
  exact basis_repr_equiv_self_explicit _ _ _ _

private theorem map_kronPowModePositionEquiv_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (e : Equiv.Perm (Fin n))
    (x : PiTensorProduct K (T.kronPow n).V)
    (w : ∀ i, Fin n → ι i) :
    (kronPowTensorWordBasisExplicit T b n).repr
        (PiTensorProduct.map
          (fun i ↦
            (kronPowModePositionEquiv T i (b i) n e).toLinearMap) x) w =
      (kronPowTensorWordBasisExplicit T b n).repr x
        ((kronPowTensorWordReindex e ι).symm w) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
      simp only [map_smul, PiTensorProduct.map_tprod,
        kronPowTensorWordBasisExplicit,
        Basis.piTensorProduct_repr_tprod_apply,
        Finsupp.smul_apply]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact kronPowModePositionEquiv_repr_explicit
        T i (b i) n e (v i) (w i)
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]

private theorem kronPowModePositionEquiv_map_t_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    PiTensorProduct.map
        (fun i ↦
          (kronPowModePositionEquiv T i (b i) n e).toLinearMap)
        (T.kronPow n).t =
      (T.kronPow n).t := by
  let B := kronPowTensorWordBasisExplicit T b n
  let E := kronPowTensorWordReindex e ι
  apply B.repr.injective
  ext w
  calc
    _ = B.repr (T.kronPow n).t (E.symm w) := by
      exact map_kronPowModePositionEquiv_repr_explicit
        T b n e (T.kronPow n).t w
    _ = B.repr (T.kronPow n).t w := by
      simp only [B, E]
      rw [kronPowTensorWordBasis_repr_explicit,
        kronPowTensorWordBasis_repr_explicit]
      simp only [kronPowTensorWordReindex,
        Equiv.piCongrRight_symm_apply, Pi.map_apply,
        kronPowWordReindex]
      change
        (∏ r : Fin n,
          (Basis.piTensorProduct b).repr T.t
            (fun i ↦ w i (e.symm r))) = _
      simpa using Equiv.prod_comp e.symm
        (fun r : Fin n ↦
          (Basis.piTensorProduct b).repr T.t (fun i ↦ w i r))

theorem solution
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    ∃ Φ : ∀ i : Fin d,
        (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i,
      (∀ (i : Fin d) (w : Fin n → ι i),
        Φ i
            (kronPowModeWordBasis T i (b i) n w) =
          kronPowModeWordBasis T i (b i) n (fun r ↦ w (e r))) ∧
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap)
          (T.kronPow n).t =
        (T.kronPow n).t := by
  let Φ : ∀ i : Fin d,
      (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i :=
    fun i ↦ kronPowModePositionEquiv T i (b i) n e
  refine ⟨Φ, ?_, ?_⟩
  · intro i w
    exact kronPowModePositionEquiv_basis_explicit T i (b i) n e w
  · exact kronPowModePositionEquiv_map_t_explicit T b n e
