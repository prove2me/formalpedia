-- Prove2me | solution 1 for mme_MMObj_restrict_scalar_bigAdd_of_induced_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:09:18.439525+00:00
-- url     : https://prove2.me/submissions/9a626636-3586-4d58-b7ba-6eb12d159276

import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Definitions.Def_mme_tensor_bridge

open MME PiTensorProduct BigOperators

universe u

set_option maxHeartbeats 1200000

theorem solution
    {K : Type u} [Field K] (H : ℕ)
    (E : Finset (Fin H × Fin H × Fin H))
    (hx : Function.Injective
      (fun e : E => (e.1.1, e.1.2.1)))
    (hy : Function.Injective
      (fun e : E => (e.1.2.1, e.1.2.2)))
    (hz : Function.Injective
      (fun e : E => (e.1.2.2, e.1.1)))
    (hinduced : ∀ x y z : E,
      x.1.2.1 = y.1.2.1 →
      y.1.2.2 = z.1.2.2 →
      z.1.1 = x.1.1 →
      x = y ∧ y = z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin E.card => MMObj K 1 1 1))
      (MMObj K H H H) := by
  classical
  let e : Fin E.card ≃ E := E.equivFin.symm
  let f : ∀ s : Fin 3,
      (MMObj K H H H).V s →ₗ[K]
        (TensorObj.diagObj K 3 E.card).V s
    | ⟨0, _⟩ => LinearMap.funLeft K K
        (fun r : Fin E.card => ((e r).1.1, (e r).1.2.1))
    | ⟨1, _⟩ => LinearMap.funLeft K K
        (fun r : Fin E.card => ((e r).1.2.1, (e r).1.2.2))
    | ⟨2, _⟩ => LinearMap.funLeft K K
        (fun r : Fin E.card => ((e r).1.2.2, (e r).1.1))
    | ⟨_ + 3, h⟩ => absurd h (by omega)
  have hdiag : TensorObj.Restrict
      (TensorObj.diagObj K 3 E.card) (MMObj K H H H) := by
    refine ⟨f, ?_⟩
    change PiTensorProduct.map f (MMObj K H H H).t =
      (TensorObj.diagObj K 3 E.card).t
    rw [MMObj_t]
    have hmap :
        PiTensorProduct.map f
            (∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H,
              MMPure K H H H i j k) =
          ∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H,
            PiTensorProduct.map f (MMPure K H H H i j k) := by
      calc
        _ = ∑ i : Fin H, PiTensorProduct.map f
              (∑ j : Fin H, ∑ k : Fin H, MMPure K H H H i j k) :=
            map_sum (PiTensorProduct.map f) _ Finset.univ
        _ = ∑ i : Fin H, ∑ j : Fin H, PiTensorProduct.map f
              (∑ k : Fin H, MMPure K H H H i j k) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact map_sum (PiTensorProduct.map f) _ Finset.univ
        _ = _ := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun j _ => ?_)
            exact map_sum (PiTensorProduct.map f) _ Finset.univ
    let v : Fin H → Fin H → Fin H →
        PiTensorProduct K (fun _ : Fin 3 => Fin E.card → K) :=
      fun i j k => PiTensorProduct.tprod K (fun s : Fin 3 =>
        f s (match s with
          | ⟨0, _⟩ =>
              (Pi.single (i, j) 1 : Fin H × Fin H → K)
          | ⟨1, _⟩ =>
              (Pi.single (j, k) 1 : Fin H × Fin H → K)
          | ⟨2, _⟩ =>
              (Pi.single (k, i) 1 : Fin H × Fin H → K)))
    have hmapPure (i j k : Fin H) :
        PiTensorProduct.map f (MMPure K H H H i j k) = v i j k := by
      dsimp only [v]
      rw [MMPure]
      exact PiTensorProduct.map_tprod f _
    calc
      _ = ∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H,
            PiTensorProduct.map f (MMPure K H H H i j k) := hmap
      _ = (TensorObj.diagObj K 3 E.card).t := by
        simp_rw [hmapPure]
        let B := Basis.piTensorProduct
          (fun _ : Fin 3 => Pi.basisFun K (Fin E.card))
        apply B.repr.injective
        ext p
        have hreprL :
            B.repr (∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H, v i j k) =
              ∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H,
                B.repr (v i j k) := by
          calc
            _ = ∑ i : Fin H, B.repr
                  (∑ j : Fin H, ∑ k : Fin H, v i j k) :=
                map_sum B.repr _ Finset.univ
            _ = ∑ i : Fin H, ∑ j : Fin H, B.repr
                  (∑ k : Fin H, v i j k) := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                exact map_sum B.repr _ Finset.univ
            _ = _ := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                refine Finset.sum_congr rfl (fun j _ => ?_)
                exact map_sum B.repr _ Finset.univ
        have hreprR :
            B.repr (TensorObj.diagObj K 3 E.card).t =
              ∑ r : Fin E.card,
                B.repr (PiTensorProduct.tprod K
                  (fun _ : Fin 3 =>
                    (Pi.single r 1 : Fin E.card → K))) := by
          change B.repr
              (∑ r : Fin E.card, PiTensorProduct.tprod K
                (fun _ : Fin 3 =>
                  (Pi.single r 1 : Fin E.card → K))) = _
          exact map_sum B.repr _ Finset.univ
        have hf0 (i j : Fin H) :
            (f (0 : Fin 3)
              (Pi.single (i, j) 1 : Fin H × Fin H → K)) (p 0) =
              (Pi.single (i, j) 1 : Fin H × Fin H → K)
                ((e (p 0)).1.1, (e (p 0)).1.2.1) := by
          rfl
        have hf1 (j k : Fin H) :
            (f (1 : Fin 3)
              (Pi.single (j, k) 1 : Fin H × Fin H → K)) (p 1) =
              (Pi.single (j, k) 1 : Fin H × Fin H → K)
                ((e (p 1)).1.2.1, (e (p 1)).1.2.2) := by
          rfl
        have hf2 (k i : Fin H) :
            (f (2 : Fin 3)
              (Pi.single (k, i) 1 : Fin H × Fin H → K)) (p 2) =
              (Pi.single (k, i) 1 : Fin H × Fin H → K)
                ((e (p 2)).1.2.2, (e (p 2)).1.1) := by
          rfl
        have hvrepr (i j k : Fin H) :
            B.repr (v i j k) p =
              (Pi.single (i, j) 1 : Fin H × Fin H → K)
                  ((e (p 0)).1.1, (e (p 0)).1.2.1) *
                (Pi.single (j, k) 1 : Fin H × Fin H → K)
                  ((e (p 1)).1.2.1, (e (p 1)).1.2.2) *
                (Pi.single (k, i) 1 : Fin H × Fin H → K)
                  ((e (p 2)).1.2.2, (e (p 2)).1.1) := by
          dsimp only [B, v]
          refine (Basis.piTensorProduct_repr_tprod_apply _ _ _).trans ?_
          rw [Fin.prod_univ_three]
          rfl
        calc
          _ = (∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H,
                B.repr (v i j k)) p :=
              congrArg (fun z => z p) hreprL
          _ = ∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H,
                (B.repr (v i j k)) p := by
              change (Finsupp.applyAddHom p)
                  (∑ i : Fin H, ∑ j : Fin H, ∑ k : Fin H,
                    B.repr (v i j k)) = _
              calc
                _ = ∑ i : Fin H, (Finsupp.applyAddHom p)
                      (∑ j : Fin H, ∑ k : Fin H,
                        B.repr (v i j k)) :=
                    map_sum (Finsupp.applyAddHom p) _ Finset.univ
                _ = ∑ i : Fin H, ∑ j : Fin H,
                      (Finsupp.applyAddHom p)
                        (∑ k : Fin H, B.repr (v i j k)) := by
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    exact map_sum (Finsupp.applyAddHom p) _ Finset.univ
                _ = _ := by
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    refine Finset.sum_congr rfl (fun j _ => ?_)
                    exact map_sum (Finsupp.applyAddHom p) _ Finset.univ
          _ = ∑ r : Fin E.card,
                (B.repr (PiTensorProduct.tprod K
                  (fun _ : Fin 3 =>
                    (Pi.single r 1 : Fin E.card → K)))) p := by
              simp_rw [hvrepr]
              dsimp only [B]
              simp only [Basis.piTensorProduct_repr_tprod_apply,
                Fin.prod_univ_three]
              simp only [Pi.basisFun_repr]
              simp only [Pi.single_apply]
              by_cases hab : (e (p 0)).1.2.1 = (e (p 1)).1.2.1
              · by_cases hbc : (e (p 1)).1.2.2 = (e (p 2)).1.2.2
                · by_cases hca : (e (p 2)).1.1 = (e (p 0)).1.1
                  · have heq := hinduced (e (p 0)) (e (p 1)) (e (p 2))
                      hab hbc hca
                    have hp01 : p 0 = p 1 := e.injective heq.1
                    have hp12 : p 1 = p 2 := e.injective heq.2
                    simp [hp01, hp12]
                    rw [Finset.sum_eq_single (e (p 2)).1.1]
                    · rw [Finset.sum_eq_single (e (p 2)).1.2.1]
                      · rw [Finset.sum_eq_single (e (p 2)).1.2.2]
                        · simp
                        · intro k _ hk
                          have hqk : (e (p 2)).1.2.2 ≠ k := Ne.symm hk
                          simp [hqk]
                        · simp
                      · intro j _ hj
                        apply Finset.sum_eq_zero
                        intro k _
                        have hqj : (e (p 2)).1.2.1 ≠ j := Ne.symm hj
                        simp [hqj]
                      · simp
                    · intro i _ hi
                      apply Finset.sum_eq_zero
                      intro j _
                      apply Finset.sum_eq_zero
                      intro k _
                      have hqi : (e (p 2)).1.1 ≠ i := Ne.symm hi
                      simp [hqi]
                    · simp
                  · have hp20 : p 2 ≠ p 0 := by
                      intro hp
                      apply hca
                      exact congrArg (fun r : Fin E.card => (e r).1.1) hp
                    have hR :
                        (∑ r : Fin E.card,
                          ((if p 0 = r then (1 : K) else 0) *
                            if p 1 = r then 1 else 0) *
                            if p 2 = r then 1 else 0) = 0 := by
                      apply Finset.sum_eq_zero
                      intro r _
                      by_cases h0 : p 0 = r
                      · have h2 : p 2 ≠ r := by
                          intro h2
                          exact hp20 (h2.trans h0.symm)
                        simp [h0, h2]
                      · simp [h0]
                    rw [hR]
                    apply Finset.sum_eq_zero
                    intro i _
                    apply Finset.sum_eq_zero
                    intro j _
                    apply Finset.sum_eq_zero
                    intro k _
                    by_cases h0 :
                        ((e (p 0)).1.1, (e (p 0)).1.2.1) = (i, j)
                    · by_cases h2 :
                          ((e (p 2)).1.2.2, (e (p 2)).1.1) = (k, i)
                      · have hai := congrArg Prod.fst h0
                        have hci := congrArg Prod.snd h2
                        exact (hca (hci.trans hai.symm)).elim
                      · simp [h2]
                    · simp [h0]
                · have hp12ne : p 1 ≠ p 2 := by
                    intro hp
                    apply hbc
                    exact congrArg (fun r : Fin E.card => (e r).1.2.2) hp
                  have hR :
                      (∑ r : Fin E.card,
                        ((if p 0 = r then (1 : K) else 0) *
                          if p 1 = r then 1 else 0) *
                          if p 2 = r then 1 else 0) = 0 := by
                    apply Finset.sum_eq_zero
                    intro r _
                    by_cases h1 : p 1 = r
                    · have h2 : p 2 ≠ r := by
                        intro h2
                        exact hp12ne (h1.trans h2.symm)
                      simp [h1, h2]
                    · simp [h1]
                  rw [hR]
                  apply Finset.sum_eq_zero
                  intro i _
                  apply Finset.sum_eq_zero
                  intro j _
                  apply Finset.sum_eq_zero
                  intro k _
                  by_cases h1 :
                      ((e (p 1)).1.2.1, (e (p 1)).1.2.2) = (j, k)
                  · by_cases h2 :
                        ((e (p 2)).1.2.2, (e (p 2)).1.1) = (k, i)
                    · have hbk := congrArg Prod.snd h1
                      have hck := congrArg Prod.fst h2
                      exact (hbc (hbk.trans hck.symm)).elim
                    · simp [h2]
                  · simp [h1]
              · have hp01ne : p 0 ≠ p 1 := by
                  intro hp
                  apply hab
                  exact congrArg (fun r : Fin E.card => (e r).1.2.1) hp
                have hR :
                    (∑ r : Fin E.card,
                      ((if p 0 = r then (1 : K) else 0) *
                        if p 1 = r then 1 else 0) *
                        if p 2 = r then 1 else 0) = 0 := by
                  apply Finset.sum_eq_zero
                  intro r _
                  by_cases h0 : p 0 = r
                  · have h1 : p 1 ≠ r := by
                      intro h1
                      exact hp01ne (h0.trans h1.symm)
                    simp [h0, h1]
                  · simp [h0]
                rw [hR]
                apply Finset.sum_eq_zero
                intro i _
                apply Finset.sum_eq_zero
                intro j _
                apply Finset.sum_eq_zero
                intro k _
                by_cases h0 :
                    ((e (p 0)).1.1, (e (p 0)).1.2.1) = (i, j)
                · by_cases h1 :
                      ((e (p 1)).1.2.1, (e (p 1)).1.2.2) = (j, k)
                  · have haj := congrArg Prod.snd h0
                    have hbj := congrArg Prod.fst h1
                    exact (hab (haj.trans hbj.symm)).elim
                  · simp [h1]
                · simp [h0]
          _ = (∑ r : Fin E.card,
                B.repr (PiTensorProduct.tprod K
                  (fun _ : Fin 3 =>
                    (Pi.single r 1 : Fin E.card → K)))) p := by
              symm
              change (Finsupp.applyAddHom p)
                (∑ r : Fin E.card,
                  B.repr (PiTensorProduct.tprod K
                    (fun _ : Fin 3 =>
                      (Pi.single r 1 : Fin E.card → K)))) = _
              exact map_sum (Finsupp.applyAddHom p) _ Finset.univ
          _ = _ := congrArg (fun z => z p) hreprR.symm
  change TensorQ.le
    (TensorQ.toQ
      (TensorObj.bigAdd (fun _ : Fin E.card => MMObj K 1 1 1)))
    (TensorQ.toQ (MMObj K H H H))
  have hdiagQ : TensorQ.le
      ((E.card : ℕ) : TensorQ K 3)
      (TensorQ.toQ (MMObj K H H H)) := by
    rw [TensorQ.natCast_eq]
    exact hdiag
  rw [TensorQ.toQ_bigAdd]
  have hone : TensorQ.toQ (MMObj K 1 1 1) =
      (1 : TensorQ K 3) := MMq_one
  simpa only [hone, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul, mul_one] using hdiagQ
