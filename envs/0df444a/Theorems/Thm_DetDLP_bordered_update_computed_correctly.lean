-- Prove2me | Theorems.Thm_DetDLP_bordered_update_computed_correctly
-- name    : DetDLP.bordered_update_computed_correctly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:49:27.618719+00:00
-- url     : https://prove2.me/theorems/f66ee755-d858-46f9-8c85-a8e0f137c81c
-- title:
--   Correctness of the executable modular coset update
-- statement:
--   For a positive modulus $m$ and an integer lattice containing $m\mathbb Z^n$, the executable bordered-column algorithm returns the Hermite basis and representative of any nonempty affine section by a single modular constraint. The trailing basis and first pivot satisfy the integer slice decomposition used in the resource-bounded machine specification.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Lemma 4.4, Section 4.3.

import Definitions.Def_DetDLP_BorderedHermite

set_option autoImplicit false

namespace DetDLP
open BorderedHermite

theorem bordered_update_computed_correctly {m n : ℕ} [NeZero m] (hm : 0 < m) (x : Fin n → ZMod m)
    (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ZMod m) (c : ZMod m)
    (hmB : ∀ v : Fin n → ℤ, (fun i => (m:ℤ)*v i) ∈ latticeSpan B) :
    let res := update m (Vector.ofFn fun i => (x i).val)
      (Vector.ofFn fun j => Vector.ofFn fun i => B i j)
      (Vector.ofFn fun i => (a i).val) c.val
    let D : Matrix (Fin n) (Fin n) ℤ := fun i j => (res.2.get j).get i
    let r : ℤ := (c-∑ i,a i*x i).val
    ∃ (d : ℤ) (u : Fin n → ℤ), 0 < d ∧ IsColumnHNF D ∧
      (∀ (z : ℤ) (y : Fin n → ℤ),
        (∃ (q : ℤ) (t : Fin n → ℤ), z=(m:ℤ)*q+∑ i,((a i).val:ℤ)*y i ∧ y=B.mulVec t) ↔
          (∃ (s : ℤ) (v : Fin n → ℤ), z=d*s ∧ y=fun i => s*u i+D.mulVec v i)) ∧
      ∀ i, res.1.get i = (x i + (((r/d)*u i : ℤ) : ZMod m)).val := by sorry
end DetDLP
