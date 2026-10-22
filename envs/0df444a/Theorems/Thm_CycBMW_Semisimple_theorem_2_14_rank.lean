-- Prove2me | Theorems.Thm_CycBMW_Semisimple_theorem_2_14_rank
-- name    : CycBMW.Semisimple.theorem_2_14_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:41.924981+00:00
-- url     : https://prove2.me/theorems/7e17b9f1-2e43-4642-9e6a-e0ba7cb9e0f5
-- title:
--   Theorem 2.14 (rank part) — $\dim_F \mathscr B_{r,n} = r^n(2n-1)!!$
-- statement:
--   Let $F$ be a field, $r \ge 1$ and $n \ge 1$, and let $q, u_1, \dots, u_r \in F$ be non-zero with $q^2 \ne 1$ (so $\delta = q - q^{-1} \ne 0$) and the $u_i$ pairwise distinct; let $\varepsilon \in \{1,-1\}$ and let $\varrho$, $\omega_a$ be the u-admissible parameters of Assumption 2.2. Then the cyclotomic Birman–Wenzl algebra $\mathscr B_{r,n}$ over $F$ is finite-dimensional and
--   $$\dim_F \mathscr B_{r,n} = r^n\,(2n-1)!!.$$
--
--   This is the rank statement of Theorem 2.14, which the paper derives from a cellular basis of $\mathscr B_{r,n}$; over a field it follows by the base change $\mathscr B_{r,n,F} \cong \mathscr B_{r,n} \otimes_R F$ of p. 6. It shows in particular that the presentation does not collapse.
--
--   **Formalization Note** The cellular-basis part of Theorem 2.14 is not stated. The sentence on p. 3 giving the rank as $r^n(2f-1)!!$ is a typo for $r^n(2n-1)!!$. $(2n-1)!!$ is `Nat.doubleFactorial (2 * n - 1)`.
-- source:
--   Rui and Si, The representation theory of cyclotomic BMW algebras, arXiv:0807.4149v1, p. 6, Theorem 2.14 (rank) and the base change B_{r,n,F} ≅ B_{r,n} ⊗_R F

import Mathlib
import Definitions.Def_CycBMW_Semisimple_Setting

namespace CycBMW.Semisimple

/-- Theorem 2.14 (rank part), p. 6, over a field: `dim_F B_{r,n} = r^n (2n-1)!!`. -/
theorem theorem_2_14_rank {F : Type*} [Field F] (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (q : F) (u : Fin r → F) (ε : ℤˣ) (hq : q ≠ 0) (hq2 : q ^ 2 ≠ 1)
    (hu : ∀ i, u i ≠ 0) (hinj : Function.Injective u) :
    Module.Finite F (B F r n q u ε) ∧
      Module.finrank F (B F r n q u ε) = r ^ n * Nat.doubleFactorial (2 * n - 1) := by sorry

end CycBMW.Semisimple
