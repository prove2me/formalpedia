-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_firmly_nonexpansive_iff_inverse_minus_id
-- name    : DouglasRachfordPPA.GenDR.firmly_nonexpansive_iff_inverse_minus_id
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:23:16.490455+00:00
-- url     : https://prove2.me/theorems/af4e7080-9f74-4960-90df-59252a8e2f9e
-- title:
--   Corollary 2.1 — $K$ is firmly nonexpansive iff $K^{-1}-I$ is monotone
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $K$ an operator on $\mathcal H$. Then
--
--   1. $K$ is firmly nonexpansive if and only if $K^{-1}-I$ is monotone;
--   2. $K$ is firmly nonexpansive with full domain if and only if $K^{-1}-I$ is maximal monotone.
--
--   This is the case $c=1$ of Theorem 2 read in the other direction: every firmly nonexpansive operator is the resolvent of the monotone operator $K^{-1}-I$.
--
--   **Formalization Note** $K^{-1}-I$ is the graph sum `opAdd (opInv K) (opSmul (-1) opId)`, i.e. $\{(y,x-y)\mid (x,y)\in K\}$; "full domain" is $\operatorname{dom}K=\mathcal H$.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 8, Corollary 2.1

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Corollary 2.1: `K` is firmly nonexpansive iff `K⁻¹ - I` is monotone; `K` is firmly
nonexpansive with full domain iff `K⁻¹ - I` is maximal monotone. -/
theorem firmly_nonexpansive_iff_inverse_minus_id {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : H → Set H) :
    (IsFirmlyNonexpansiveOp K ↔ IsMonotoneOp (opAdd (opInv K) (opSmul (-1) opId))) ∧
    (IsFirmlyNonexpansiveOp K ∧ dom K = Set.univ ↔
      IsMaximalMonotone (opAdd (opInv K) (opSmul (-1) opId))) := by sorry

end DouglasRachfordPPA.GenDR
