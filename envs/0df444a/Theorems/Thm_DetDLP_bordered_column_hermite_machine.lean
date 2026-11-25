-- Prove2me | Theorems.Thm_DetDLP_bordered_column_hermite_machine
-- name    : DetDLP.bordered_column_hermite_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:19:24.298731+00:00
-- url     : https://prove2.me/theorems/62dff3d6-d39b-40d7-bd81-d268fda14045
-- title:
--   Polynomial-bit computation and projection of a bordered column Hermite form
-- statement:
--   Let $B$ be an integer matrix with $N$ rows and columns, with $|B_{ij}|\le m$ and $m\mathbb Z^N\subseteq B\mathbb Z^N$. Let $a,x\in(\mathbb Z/m)^N$ and $c\in\mathbb Z/m$. Write $r$ for the least nonnegative lift of $c-a^Tx$ and let $\widetilde a$ be the vector of least nonnegative lifts of $a$. Compute the bordered column Hermite decomposition
--   $$
--   \{(m q+\widetilde a^T Bt,Bt):q\in\mathbb Z,\;t\in\mathbb Z^N\}
--   =\{(ds,su+Dv):s\in\mathbb Z,\;v\in\mathbb Z^N\}.
--   $$
--   Here $d>0$ and $D$ is in lower-triangular column Hermite form. A uniform binary multitape machine outputs $x+\lfloor r/d\rfloor u\pmod m$ and $D$ in time and space polynomial in $N+\lceil\log_2 m\rceil$. The conclusion applies also to offsets outside the image. It is a matrix normalization routine with a specified output projection.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Section 4.3, Lemma 4.4 (auxiliary bordered Hermite form computation).

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem bordered_column_hermite_machine :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (m N : ℕ) [NeZero m], 2 ≤ m → 1 ≤ N →
      ∀ (x : Fin N → ZMod m) (B : Matrix (Fin N) (Fin N) ℤ)
        (a : Fin N → ZMod m) (c : ZMod m), (∀ i j, |B i j| ≤ (m:ℤ)) →
      (∀ v : Fin N → ℤ, (fun i => (m:ℤ)*v i) ∈ latticeSpan B) →
      let f := fun y : Fin N → ℤ => ∑ i, ((a i).val : ℤ)*y i
      let r : ℤ := (c - ∑ i, a i*x i).val
      ∃ (d : ℤ) (u : Fin N → ℤ) (D : Matrix (Fin N) (Fin N) ℤ),
        0 < d ∧ IsColumnHNF D ∧
        (∀ (z : ℤ) (y : Fin N → ℤ),
          (∃ (q : ℤ) (t : Fin N → ℤ), z = (m : ℤ)*q + f y ∧ y = B.mulVec t) ↔
          (∃ (s : ℤ) (v : Fin N → ℤ), z = d*s ∧ y = fun i => s*u i + D.mulVec v i)) ∧
        RunsWithin M out
          (encodeCosetUpdateInput m (fun i => (x i).val) B (fun i => (a i).val) c.val)
          (encodeCosetRep (fun i => (x i+(((r/d)*u i : ℤ) : ZMod m)).val) D)
          (polyBound K (N + bitLen m)) (polyBound K (N + bitLen m)) := by sorry

end DetDLP
