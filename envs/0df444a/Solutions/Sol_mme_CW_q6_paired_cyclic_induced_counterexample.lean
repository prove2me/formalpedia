-- Prove2me | solution 1 for mme_CW_q6_paired_cyclic_induced_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:34:44.465552+00:00
-- url     : https://prove2.me/submissions/b2c19f23-2869-407d-b4e8-465b404413e7

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Tactic

open MME

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Counterexample

def address0 : CWQ6CoupledAddress 2 :=
  ![![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 2, 2]]

def address1 : CWQ6CoupledAddress 2 :=
  ![![0, 1, 1, 0], ![1, 0, 1, 0], ![2, 2, 1, 0]]

def exact0 : CWQ6ExactCoupledAddress 2 1 1 :=
  ⟨address0, by
    constructor
    · intro j
      fin_cases j <;> simp [address0]
    · intro i r
      fin_cases i <;> fin_cases r <;> decide⟩

def exact1 : CWQ6ExactCoupledAddress 2 1 1 :=
  ⟨address1, by
    constructor
    · intro j
      fin_cases j <;> simp [address1]
    · intro i r
      fin_cases i <;> fin_cases r <;> decide⟩

def entry : Fin 2 × Fin 1 → CWQ6ExactCoupledAddress 2 1 1 :=
  fun p ↦ ![exact0, exact1] p.1

def family : CWQ6PrimaryHashFamily 2 1 1 2 1 where
  hHpos := by omega
  entry := entry
  xInjective := by decide
  yInjective := by decide
  zSameFiber := by decide
  zSeparatesFibers := by decide
  induced := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩ hsupp
    fin_cases p <;> fin_cases hp <;>
      fin_cases q <;> fin_cases hq <;>
      fin_cases r <;> fin_cases hr <;>
      simp [CWQ6CoupledCoordinatewiseSupported, cwQ6CoupledMixedAddress,
        entry, exact0, exact1, address0, address1] at hsupp ⊢
    all_goals
      have h0 := hsupp (0 : Fin 4)
      have h1 := hsupp (1 : Fin 4)
      have h2 := hsupp (2 : Fin 4)
      have h3 := hsupp (3 : Fin 4)
      simp at h0 h1 h2 h3

def halving : family.CommonBalancedXYHalving where
  half := 1
  even_length := by omega
  position := finSumFinEquiv
  first_x := by decide
  second_y := by decide

def p0 : Fin 2 × Fin 1 := (0, 0)
def p1 : Fin 2 × Fin 1 := (1, 0)

theorem supported_001 :
    family.PairedCyclicSupported halving p0 p0 p1 := by
  constructor <;> intro r <;> fin_cases r <;>
    simp only [CWQ6CoupledLocalSupported] <;> decide

theorem not_paired : ¬ family.PairedCyclicInduced halving := by
  intro h
  have hdiag := h p0 p0 p1 supported_001
  exact (by decide : p0 ≠ p1) hdiag.2

end Counterexample

theorem solution :
    ∃ family : CWQ6PrimaryHashFamily 2 1 1 2 1,
      ∃ halving : family.CommonBalancedXYHalving,
        ¬ family.PairedCyclicInduced halving := by
  exact ⟨Counterexample.family, Counterexample.halving,
    Counterexample.not_paired⟩
