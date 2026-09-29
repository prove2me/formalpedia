-- Prove2me | solution 1 for mme_dwz_coarseClassBasis_q6_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:34:01.514355+00:00
-- url     : https://prove2.me/submissions/540a0b6d-e73a-422d-8106-13de6a93a49e

import Definitions.Def_mme_dwz_component_word_projection

open MME Module

universe u v

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace CoarseBasisQ6Solution

theorem basis_cast_apply_coe
    {K V : Type u} {I : Type v} [Field K] [AddCommGroup V] [Module K V]
    {P Q : Submodule K V} (h : P = Q) (b : Basis I K P) (i : I) :
    ((cast (congrArg (fun R : Submodule K V ↦ Basis I K R) h) b) i : V) =
      (b i : V) := by
  subst Q
  rfl

end CoarseBasisQ6Solution

theorem solution
    (K : Type u) [Field K] (i : Fin 3) (c : Fin 5)
    (p : MME.DWZComponentRestriction.CoarsePair 6 c) :
    (MME.DWZComponentRestriction.coarseClassBasis
      (K := K) 6 i c p).1 =
      cwSquareCanonicalBasis K 6 i p.1 := by
  open MME.DWZComponentRestriction in
    let b := cwSquareCanonicalBasis K 6 i
    let v : CoarsePair 6 c →
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i) := fun p ↦ b p.1
    have hv : LinearIndependent K v := by
      simpa [v, Function.comp_def] using
        b.linearIndependent.comp (fun p : CoarsePair 6 c ↦ p.1)
          Subtype.val_injective
    have hset : Set.range v =
        b '' {p | cwSquarePairGrade 6 p = c} := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.1, p.2, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hp⟩, rfl⟩
    have hsub :
        cwBasisGrade (cwSquareCanonicalBasis K 6 i)
            (cwSquarePairGrade 6) c =
          Submodule.span K (Set.range v) := by
      unfold cwBasisGrade
      simpa only [b] using congrArg (Submodule.span K) hset.symm
    unfold coarseClassBasis
    dsimp only
    change ((((Eq.mpr
        (congrArg
          (fun R : Submodule K
              ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i) ↦
            Basis (CoarsePair 6 c) K R) hsub)
        (Basis.span hv)) :
        Basis (CoarsePair 6 c) K
          (cwBasisGrade (cwSquareCanonicalBasis K 6 i)
            (cwSquarePairGrade 6) c)) p).1) = _
    have hcast :
        ((((Eq.mpr
          (congrArg
            (fun R : Submodule K
                ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i) ↦
              Basis (CoarsePair 6 c) K R) hsub)
          (Basis.span hv)) :
          Basis (CoarsePair 6 c) K
            (cwBasisGrade (cwSquareCanonicalBasis K 6 i)
              (cwSquarePairGrade 6) c)) p).1) =
          ((Basis.span hv p : Submodule.span K (Set.range v)) :
            ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i)) := by
      exact CoarseBasisQ6Solution.basis_cast_apply_coe
        (K := K)
        (V := ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i))
        (I := CoarsePair 6 c)
        (P := Submodule.span K (Set.range v))
        (Q := cwBasisGrade (cwSquareCanonicalBasis K 6 i)
          (cwSquarePairGrade 6) c)
        hsub.symm (Basis.span hv) p
    calc
      _ = ((Basis.span hv p : Submodule.span K (Set.range v)) :
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i)) := hcast
      _ = v p := by rw [Basis.span_apply]
      _ = cwSquareCanonicalBasis K 6 i p.1 := rfl
