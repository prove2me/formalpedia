-- Prove2me | solution 1 for mme_stothers_phi233_canonical_cyclic_mode_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:02:05.613833+00:00
-- url     : https://prove2.me/submissions/861cc378-6578-4cf1-8b64-28527db0de02

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option warningAsError true

private def tripleFiberEquiv
    {A X Y Z : Type} (f : A → X) (g : A → Y) (h : A → Z)
    (a b c : A) :
    {e : A × (A × A) //
        (f e.1, (g e.2.1, h e.2.2)) = (f a, (g b, h c))} ≃
      {x : A // f x = f a} ×
        ({y : A // g y = g b} × {z : A // h z = h c}) where
  toFun e :=
    (⟨e.1.1, congrArg (fun w ↦ w.1) e.2⟩,
      (⟨e.1.2.1, congrArg (fun w ↦ w.2.1) e.2⟩,
        ⟨e.1.2.2, congrArg (fun w ↦ w.2.2) e.2⟩))
  invFun x := ⟨(x.1.1, (x.2.1.1, x.2.2.1)), by
    apply Prod.ext
    · exact x.1.2
    · apply Prod.ext
      · exact x.2.1.2
      · exact x.2.2.2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv x := by rfl

/-- A cyclic mode fixes one word in each ordinary mode.  Consequently its
ambient and exact fibers are products of the three ordinary fixed-word
stars (the cyclic permutation does not change the product). -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        {e : MME.StothersFourth.Phi233.CyclicAmbientEdge
            N alpha beta gamma delta //
          MME.StothersFourth.Phi233.cyclicModeWord e i =
            MME.StothersFourth.Phi233.cyclicModeWord
              (a.1, (a.1, a.1)) i} =
      ∏ l : Fin 3,
        Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 l = a.1.1 l} ∧
    Nat.card
        {e : MME.StothersFourth.Phi233.CyclicExactEdge
            N alpha beta gamma delta //
          MME.StothersFourth.Phi233.cyclicModeWord
              (MME.StothersFourth.Phi233.exactToAmbient e) i =
            MME.StothersFourth.Phi233.cyclicModeWord
              (a.1, (a.1, a.1)) i} =
      ∏ l : Fin 3,
        Nat.card
          {b : MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta // b.1.1 l = a.1.1 l} := by
  let Marginal := MME.StothersFourth.Phi233.MarginalAddress
    N alpha beta gamma delta
  let Exact := MME.StothersFourth.Phi233.ExactProfileAddress
    N alpha beta gamma delta
  have hamb : Nat.card
      {e : MME.StothersFourth.Phi233.CyclicAmbientEdge
          N alpha beta gamma delta //
        MME.StothersFourth.Phi233.cyclicModeWord e i =
          MME.StothersFourth.Phi233.cyclicModeWord
            (a.1, (a.1, a.1)) i} =
      ∏ l : Fin 3,
        Nat.card {b : Marginal // b.1 l = a.1.1 l} := by
    fin_cases i
    · let e := tripleFiberEquiv
        (fun b : Marginal ↦ b.1 (0 : Fin 3))
        (fun b : Marginal ↦ b.1 (2 : Fin 3))
        (fun b : Marginal ↦ b.1 (1 : Fin 3)) a.1 a.1 a.1
      calc
        Nat.card
            {x : MME.StothersFourth.Phi233.CyclicAmbientEdge
                N alpha beta gamma delta //
              MME.StothersFourth.Phi233.cyclicModeWord x 0 =
                MME.StothersFourth.Phi233.cyclicModeWord
                  (a.1, (a.1, a.1)) 0} =
            Nat.card
              ({b : Marginal // b.1 0 = a.1.1 0} ×
                ({b : Marginal // b.1 2 = a.1.1 2} ×
                  {b : Marginal // b.1 1 = a.1.1 1})) := by
          exact Nat.card_congr e
        _ = Nat.card {b : Marginal // b.1 0 = a.1.1 0} *
              (Nat.card {b : Marginal // b.1 1 = a.1.1 1} *
                Nat.card {b : Marginal // b.1 2 = a.1.1 2}) := by
          simp only [Nat.card_prod]
          ac_rfl
        _ = ∏ l : Fin 3,
            Nat.card {b : Marginal // b.1 l = a.1.1 l} := by
          simp [Fin.prod_univ_succ]
    · let e := tripleFiberEquiv
        (fun b : Marginal ↦ b.1 (1 : Fin 3))
        (fun b : Marginal ↦ b.1 (0 : Fin 3))
        (fun b : Marginal ↦ b.1 (2 : Fin 3)) a.1 a.1 a.1
      calc
        Nat.card
            {x : MME.StothersFourth.Phi233.CyclicAmbientEdge
                N alpha beta gamma delta //
              MME.StothersFourth.Phi233.cyclicModeWord x 1 =
                MME.StothersFourth.Phi233.cyclicModeWord
                  (a.1, (a.1, a.1)) 1} =
            Nat.card
              ({b : Marginal // b.1 1 = a.1.1 1} ×
                ({b : Marginal // b.1 0 = a.1.1 0} ×
                  {b : Marginal // b.1 2 = a.1.1 2})) := by
          exact Nat.card_congr e
        _ = Nat.card {b : Marginal // b.1 0 = a.1.1 0} *
              (Nat.card {b : Marginal // b.1 1 = a.1.1 1} *
                Nat.card {b : Marginal // b.1 2 = a.1.1 2}) := by
          simp only [Nat.card_prod]
          ac_rfl
        _ = ∏ l : Fin 3,
            Nat.card {b : Marginal // b.1 l = a.1.1 l} := by
          simp [Fin.prod_univ_succ]
    · let e := tripleFiberEquiv
        (fun b : Marginal ↦ b.1 (2 : Fin 3))
        (fun b : Marginal ↦ b.1 (1 : Fin 3))
        (fun b : Marginal ↦ b.1 (0 : Fin 3)) a.1 a.1 a.1
      calc
        Nat.card
            {x : MME.StothersFourth.Phi233.CyclicAmbientEdge
                N alpha beta gamma delta //
              MME.StothersFourth.Phi233.cyclicModeWord x 2 =
                MME.StothersFourth.Phi233.cyclicModeWord
                  (a.1, (a.1, a.1)) 2} =
            Nat.card
              ({b : Marginal // b.1 2 = a.1.1 2} ×
                ({b : Marginal // b.1 1 = a.1.1 1} ×
                  {b : Marginal // b.1 0 = a.1.1 0})) := by
          exact Nat.card_congr e
        _ = Nat.card {b : Marginal // b.1 0 = a.1.1 0} *
              (Nat.card {b : Marginal // b.1 1 = a.1.1 1} *
                Nat.card {b : Marginal // b.1 2 = a.1.1 2}) := by
          simp only [Nat.card_prod]
          ac_rfl
        _ = ∏ l : Fin 3,
            Nat.card {b : Marginal // b.1 l = a.1.1 l} := by
          simp [Fin.prod_univ_succ]
  have htarget : Nat.card
      {e : MME.StothersFourth.Phi233.CyclicExactEdge
          N alpha beta gamma delta //
        MME.StothersFourth.Phi233.cyclicModeWord
            (MME.StothersFourth.Phi233.exactToAmbient e) i =
          MME.StothersFourth.Phi233.cyclicModeWord
            (a.1, (a.1, a.1)) i} =
      ∏ l : Fin 3,
        Nat.card {b : Exact // b.1.1 l = a.1.1 l} := by
    fin_cases i
    · let e := tripleFiberEquiv
        (fun b : Exact ↦ b.1.1 (0 : Fin 3))
        (fun b : Exact ↦ b.1.1 (2 : Fin 3))
        (fun b : Exact ↦ b.1.1 (1 : Fin 3)) a a a
      calc
        Nat.card
            {x : MME.StothersFourth.Phi233.CyclicExactEdge
                N alpha beta gamma delta //
              MME.StothersFourth.Phi233.cyclicModeWord
                  (MME.StothersFourth.Phi233.exactToAmbient x) 0 =
                MME.StothersFourth.Phi233.cyclicModeWord
                  (a.1, (a.1, a.1)) 0} =
            Nat.card
              ({b : Exact // b.1.1 0 = a.1.1 0} ×
                ({b : Exact // b.1.1 2 = a.1.1 2} ×
                  {b : Exact // b.1.1 1 = a.1.1 1})) := by
          exact Nat.card_congr e
        _ = Nat.card {b : Exact // b.1.1 0 = a.1.1 0} *
              (Nat.card {b : Exact // b.1.1 1 = a.1.1 1} *
                Nat.card {b : Exact // b.1.1 2 = a.1.1 2}) := by
          simp only [Nat.card_prod]
          ac_rfl
        _ = ∏ l : Fin 3,
            Nat.card {b : Exact // b.1.1 l = a.1.1 l} := by
          simp [Fin.prod_univ_succ]
    · let e := tripleFiberEquiv
        (fun b : Exact ↦ b.1.1 (1 : Fin 3))
        (fun b : Exact ↦ b.1.1 (0 : Fin 3))
        (fun b : Exact ↦ b.1.1 (2 : Fin 3)) a a a
      calc
        Nat.card
            {x : MME.StothersFourth.Phi233.CyclicExactEdge
                N alpha beta gamma delta //
              MME.StothersFourth.Phi233.cyclicModeWord
                  (MME.StothersFourth.Phi233.exactToAmbient x) 1 =
                MME.StothersFourth.Phi233.cyclicModeWord
                  (a.1, (a.1, a.1)) 1} =
            Nat.card
              ({b : Exact // b.1.1 1 = a.1.1 1} ×
                ({b : Exact // b.1.1 0 = a.1.1 0} ×
                  {b : Exact // b.1.1 2 = a.1.1 2})) := by
          exact Nat.card_congr e
        _ = Nat.card {b : Exact // b.1.1 0 = a.1.1 0} *
              (Nat.card {b : Exact // b.1.1 1 = a.1.1 1} *
                Nat.card {b : Exact // b.1.1 2 = a.1.1 2}) := by
          simp only [Nat.card_prod]
          ac_rfl
        _ = ∏ l : Fin 3,
            Nat.card {b : Exact // b.1.1 l = a.1.1 l} := by
          simp [Fin.prod_univ_succ]
    · let e := tripleFiberEquiv
        (fun b : Exact ↦ b.1.1 (2 : Fin 3))
        (fun b : Exact ↦ b.1.1 (1 : Fin 3))
        (fun b : Exact ↦ b.1.1 (0 : Fin 3)) a a a
      calc
        Nat.card
            {x : MME.StothersFourth.Phi233.CyclicExactEdge
                N alpha beta gamma delta //
              MME.StothersFourth.Phi233.cyclicModeWord
                  (MME.StothersFourth.Phi233.exactToAmbient x) 2 =
                MME.StothersFourth.Phi233.cyclicModeWord
                  (a.1, (a.1, a.1)) 2} =
            Nat.card
              ({b : Exact // b.1.1 2 = a.1.1 2} ×
                ({b : Exact // b.1.1 1 = a.1.1 1} ×
                  {b : Exact // b.1.1 0 = a.1.1 0})) := by
          exact Nat.card_congr e
        _ = Nat.card {b : Exact // b.1.1 0 = a.1.1 0} *
              (Nat.card {b : Exact // b.1.1 1 = a.1.1 1} *
                Nat.card {b : Exact // b.1.1 2 = a.1.1 2}) := by
          simp only [Nat.card_prod]
          ac_rfl
        _ = ∏ l : Fin 3,
            Nat.card {b : Exact // b.1.1 l = a.1.1 l} := by
          simp [Fin.prod_univ_succ]
  exact ⟨hamb, htarget⟩
