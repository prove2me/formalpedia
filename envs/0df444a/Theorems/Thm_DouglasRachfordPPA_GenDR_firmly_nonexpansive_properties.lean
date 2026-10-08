-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_firmly_nonexpansive_properties
-- name    : DouglasRachfordPPA.GenDR.firmly_nonexpansive_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:22:26.289255+00:00
-- url     : https://prove2.me/theorems/4613d883-6024-4704-9adb-e18e6fe7ad4f
-- title:
--   Lemma 1 — properties of firmly nonexpansive operators
-- statement:
--   Let $\mathcal H$ be a real Hilbert space. For operators on $\mathcal H$ (subsets of $\mathcal H\times\mathcal H$):
--
--   1. Every firmly nonexpansive operator is nonexpansive.
--   2. An operator $J$ is firmly nonexpansive if and only if $2J-I$ is nonexpansive.
--   3. An operator $J$ is firmly nonexpansive if and only if $J=\tfrac12(C+I)$ for some nonexpansive operator $C$.
--   4. An operator $J$ is firmly nonexpansive if and only if $I-J$ is firmly nonexpansive.
--
--   Here $2J-I$, $\tfrac12(C+I)$ and $I-J$ are formed with the graph operations of scaling and sum, so for example $2J-I=\{(x,2y-x)\mid (x,y)\in J\}$. These facts are used in the convergence proofs of Theorems 3 and 7 (through $I-J_{cT}$ and the nonexpansiveness of resolvents).
--
--   **Formalization Note** $2J-I$ is `opAdd (opSmul 2 J) (opSmul (-1) opId)`, $I-J$ is `opAdd opId (opSmul (-1) J)` and $\tfrac12(C+I)$ is `opSmul (1/2) (opAdd C opId)`; equality of operators in part 3 is equality of graphs. The four parts are one conjunction.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 5, Lemma 1 (i)–(iv)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Lemma 1: (i) firmly nonexpansive implies nonexpansive; (ii) `J` is firmly nonexpansive iff
`2J - I` is nonexpansive; (iii) `J` is firmly nonexpansive iff `J = (1/2)(C + I)` for a
nonexpansive `C`; (iv) `J` is firmly nonexpansive iff `I - J` is firmly nonexpansive.
All operations are the graph operations of p. 4. -/
theorem firmly_nonexpansive_properties
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J → IsNonexpansiveOp J) ∧
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J ↔
      IsNonexpansiveOp (opAdd (opSmul 2 J) (opSmul (-1) opId))) ∧
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J ↔
      ∃ C : H → Set H, IsNonexpansiveOp C ∧ J = opSmul (1 / 2) (opAdd C opId)) ∧
    (∀ J : H → Set H, IsFirmlyNonexpansiveOp J ↔
      IsFirmlyNonexpansiveOp (opAdd opId (opSmul (-1) J))) := by sorry

end DouglasRachfordPPA.GenDR
