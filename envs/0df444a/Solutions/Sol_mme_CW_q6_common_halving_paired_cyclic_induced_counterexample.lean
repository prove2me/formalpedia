-- Prove2me | solution 1 for mme_CW_q6_common_halving_paired_cyclic_induced_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:32.510468+00:00
-- url     : https://prove2.me/submissions/16ca161b-b324-4d88-8b49-0e4d4f1c133a

import Mathlib
import Definitions.Def_mme_CW_q6_paired_cyclic_induced

open MME
set_option autoImplicit false

namespace PairedCounterexample

def raw (a : Fin 2) : CWQ6CoupledAddress 2 :=
  if a = 0 then
    ![![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 2, 2]]
  else
    ![![0, 1, 1, 0], ![1, 0, 1, 0], ![2, 2, 1, 0]]

def address (a : Fin 2) : CWQ6ExactCoupledAddress 2 1 1 :=
  ⟨raw a, by
    fin_cases a <;>
      simp only [CWQ6CoupledCoordinatewiseSupported, cwQ6CoupledMarginalMultiplicity, raw] <;>
      decide⟩

def family : CWQ6PrimaryHashFamily 2 1 1 2 1 where
  hHpos := by decide
  entry p := address p.1
  xInjective := by
    change Function.Injective (fun p : Fin 2 × Fin 1 ↦ raw p.1 0)
    decide
  yInjective := by
    change Function.Injective (fun p : Fin 2 × Fin 1 ↦ raw p.1 1)
    decide
  zSameFiber := by intros; rfl
  zSeparatesFibers := by
    change ∀ (a b : Fin 2) (_ _ : Fin 1), raw a 2 = raw b 2 → a = b
    decide
  induced := by
    change ∀ p q r : Fin 2 × Fin 1,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress (raw p.1) (raw q.1) (raw r.1)) →
      p = q ∧ p.1 = r.1
    unfold CWQ6CoupledCoordinatewiseSupported cwQ6CoupledMixedAddress
    decide

def halving : family.CommonBalancedXYHalving where
  half := 1
  even_length := by decide
  position := finSumFinEquiv
  first_x := by
    change ∀ (p : Fin 2 × Fin 1) (grade : Fin 3),
      Fintype.card {j : Fin 2 // raw p.1 0 (finSumFinEquiv (Sum.inl j)) = grade} =
        if grade = 0 then 1 else if grade = 1 then 1 else 0
    decide
  second_y := by
    change ∀ (p : Fin 2 × Fin 1) (grade : Fin 3),
      Fintype.card {j : Fin 2 // raw p.1 1 (finSumFinEquiv (Sum.inr j)) = grade} =
        if grade = 0 then 1 else if grade = 1 then 1 else 0
    decide

theorem not_induced : ¬ family.PairedCyclicInduced halving := by
  intro h
  have hs : family.PairedCyclicSupported halving (0, 0) (0, 0) (1, 0) := by
    unfold CWQ6PrimaryHashFamily.PairedCyclicSupported CWQ6CoupledLocalSupported
    decide
  have heq := (h (0, 0) (0, 0) (1, 0) hs).2
  have hfirst := congrArg Prod.fst heq
  norm_num at hfirst

end PairedCounterexample

theorem solution :
    ∃ family : CWQ6PrimaryHashFamily 2 1 1 2 1,
      ∃ halving : family.CommonBalancedXYHalving,
        ¬ family.PairedCyclicInduced halving := by
  exact ⟨PairedCounterexample.family, PairedCounterexample.halving,
    PairedCounterexample.not_induced⟩
