-- Prove2me | solution 1 for mme_dwz_table2_component_words_equation22_distinct_outer_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T18:27:15.85758+00:00
-- url     : https://prove2.me/submissions/b9568c4c-3a8a-4666-aed3-1c5ed5aeda43

import Theorems.Thm_mme_dwz_table2_component_words_supply_outer_layout
import Theorems.Thm_mme_dwz_table2_equation22_outer_layout_compatibility_rate

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m)
    {Outer Position : Type*}
    [Finite Outer] [Nonempty Outer]
    [Fintype Position]
    (K : Position → Fin 5)
    (shapeWord : Outer → Position → Fin 15)
    (hshape : ∀ (I : Outer) (s : Fin 15),
      Fintype.card {t : Position // shapeWord I t = s} =
        MME.DWZTable2Counts.component s * m)
    (hmatch : ∀ (I : Outer) (t : Position),
      MME.DWZSquare.shapeZ (shapeWord I t) = K t) :
    let BtypicalK :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    ∃ assemble :
        (Σ _I : Outer, MME.DWZTable2Cardinality.SplitAssignments m) →
          BtypicalK,
      (∀ I, Function.Injective (fun A ↦ assemble ⟨I, A⟩)) ∧
      ∃ small : BtypicalK,
        (Nat.card Outer : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ≤
          ((6 * ((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 5 *
            (∏ s : Fin 15,
              if MME.DWZSquare.shapeX s = 0 ∨
                  MME.DWZSquare.shapeY s = 0 then
                (6 *
                  ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
              else 1) *
            (∏ k : Fin 5,
              (6 *
                ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3)) *
            (Nat.card
              {I : Outer //
                ∃ A : MME.DWZTable2Cardinality.SplitAssignments m,
                  assemble ⟨I, A⟩ = small} : ℝ) := by
  obtain ⟨layout, hlayout⟩ :=
    mme_dwz_table2_component_words_supply_outer_layout
      m K shapeWord hshape hmatch
  exact mme_dwz_table2_equation22_outer_layout_compatibility_rate
    m hm K layout hlayout
