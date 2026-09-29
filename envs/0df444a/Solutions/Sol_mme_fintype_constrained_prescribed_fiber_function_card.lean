-- Prove2me | solution 1 for mme_fintype_constrained_prescribed_fiber_function_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:40:32.3519+00:00
-- url     : https://prove2.me/submissions/951d8ffe-7826-4a56-b34b-78ecab752da2

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false

theorem solution
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (h : alpha → iota) (q : beta → iota) (k : beta → ℕ)
    (hsum : ∀ i,
      (∑ b : {b : beta // q b = i}, k b.1) =
        Fintype.card {a : alpha // h a = i}) :
    Nat.card
        {g : alpha → beta //
          (∀ a, q (g a) = h a) ∧
          ∀ b, Fintype.card {a // g a = b} = k b} =
      ∏ i,
        (Fintype.card {a : alpha // h a = i}).factorial /
          ∏ b : {b : beta // q b = i}, (k b.1).factorial := by
  classical
  let A : iota → Type _ := fun i => {a : alpha // h a = i}
  let B : iota → Type _ := fun i => {b : beta // q b = i}
  let K : ∀ i, B i → ℕ := fun _ b => k b.1

  let sectionEquiv :
      {g : alpha → beta // ∀ a, q (g a) = h a} ≃
        ∀ i, A i → B i := {
    toFun g i a := ⟨g.1 a.1, (g.2 a.1).trans a.2⟩
    invFun G := ⟨fun a => (G (h a) ⟨a, rfl⟩).1, fun a => by
      exact (G (h a) ⟨a, rfl⟩).2⟩
    left_inv g := by
      apply Subtype.ext
      funext a
      rfl
    right_inv G := by
      funext i a
      apply Subtype.ext
      obtain ⟨a, ha⟩ := a
      subst ha
      rfl
  }

  have hfiber (g : {g : alpha → beta // ∀ a, q (g a) = h a})
      (i : iota) (b : B i) :
      Fintype.card {a : A i // sectionEquiv g i a = b} =
        Fintype.card {a : alpha // g.1 a = b.1} := by
    let e : {a : A i // sectionEquiv g i a = b} ≃
        {a : alpha // g.1 a = b.1} := {
      toFun a := ⟨a.1.1, congrArg Subtype.val a.2⟩
      invFun a := by
        have haBase : h a.1 = i := by
          calc
            h a.1 = q (g.1 a.1) := (g.2 a.1).symm
            _ = q b.1 := congrArg q a.2
            _ = i := b.2
        exact ⟨⟨a.1, haBase⟩, Subtype.ext a.2⟩
      left_inv a := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv a := by
        apply Subtype.ext
        rfl
    }
    exact Fintype.card_congr e

  let goodEquiv :
      {g : alpha → beta //
        (∀ a, q (g a) = h a) ∧
        ∀ b, Fintype.card {a // g a = b} = k b} ≃
      {G : ∀ i, A i → B i //
        ∀ i b, Fintype.card {a // G i a = b} = K i b} := {
    toFun g := by
      let gs : {g : alpha → beta // ∀ a, q (g a) = h a} :=
        ⟨g.1, g.2.1⟩
      refine ⟨sectionEquiv gs, ?_⟩
      intro i b
      rw [hfiber gs i b]
      exact g.2.2 b.1
    invFun G := by
      let gs := sectionEquiv.symm G.1
      refine ⟨gs.1, gs.2, ?_⟩
      intro b
      let bi : B (q b) := ⟨b, rfl⟩
      have hb := G.2 (q b) bi
      have hsec : sectionEquiv gs = G.1 :=
        sectionEquiv.apply_symm_apply G.1
      rw [← hsec] at hb
      rw [hfiber gs (q b) bi] at hb
      simpa only [K, bi] using hb
    left_inv g := by
      apply Subtype.ext
      change
        (sectionEquiv.symm (sectionEquiv
          (⟨g.1, g.2.1⟩ : {g : alpha → beta // ∀ a, q (g a) = h a}))).1 = g.1
      exact congrArg Subtype.val
        (sectionEquiv.left_inv ⟨g.1, g.2.1⟩)
    right_inv G := by
      apply Subtype.ext
      exact sectionEquiv.right_inv G.1
  }

  let splitEquiv :
      {G : ∀ i, A i → B i //
        ∀ i b, Fintype.card {a // G i a = b} = K i b} ≃
      ∀ i, {g : A i → B i //
        ∀ b, Fintype.card {a // g a = b} = K i b} := {
    toFun G i := ⟨G.1 i, G.2 i⟩
    invFun G := ⟨fun i => (G i).1, fun i => (G i).2⟩
    left_inv G := by rfl
    right_inv G := by
      funext i
      exact Subtype.ext rfl
  }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr goodEquiv,
    Fintype.card_congr splitEquiv, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [A, B, K] using
    (mme_fintype_prescribed_fiber_function_card (K i) (by
      simpa only [A, B, K] using hsum i))
