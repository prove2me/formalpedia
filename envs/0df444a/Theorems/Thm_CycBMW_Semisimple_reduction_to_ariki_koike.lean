-- Prove2me | Theorems.Thm_CycBMW_Semisimple_reduction_to_ariki_koike
-- name    : CycBMW.Semisimple.reduction_to_ariki_koike
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:42.951957+00:00
-- url     : https://prove2.me/theorems/b9ba10bf-81b3-4b6c-a4fd-810020b9328a
-- title:
--   Proof of Theorem 6.8 — $\mathscr B_{r,n}$ is not semisimple if $\mathscr H_{r,n}$ is not semisimple
-- statement:
--   Let $F$ be a field, $r \ge 2$, $n \ge 2$, $q, u_1,\dots,u_r \in F$ non-zero with $q^2 \ne 1$ and the $u_i$ pairwise distinct, $\varepsilon \in \{1,-1\}$, and u-admissible parameters as in Assumption 2.2. Let $\mathscr H_{r,n}$ be the Ariki–Koike algebra with the same $q$ and $u_1,\dots,u_r$. Then
--   $$\mathscr H_{r,n} \text{ not semisimple} \implies \mathscr B_{r,n} \text{ not semisimple}.$$
--
--   In the paper this is the first step of the proof of Theorem 6.8: it reduces the semisimplicity of $\mathscr B_{r,n}$ to the case where $\mathscr H_{r,n}$ is semisimple, which Ariki's criterion describes by conditions (a) and (b) of Theorem 6.8(b)(2).
--
--   **Formalization Note** "Semisimple" is Mathlib's `IsSemisimpleRing`.
-- source:
--   Rui and Si, The representation theory of cyclotomic BMW algebras, arXiv:0807.4149v1, p. 25, proof of Theorem 6.8; p. 3, Ariki–Koike algebra

import Mathlib
import Definitions.Def_CycBMW_Semisimple_Setting

namespace CycBMW.Semisimple

/-- Proof of Theorem 6.8, p. 25: `B_{r,n}` is not semisimple if `H_{r,n}` is not semisimple. -/
theorem reduction_to_ariki_koike {F : Type*} [Field F] (r n : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n)
    (q : F) (u : Fin r → F) (ε : ℤˣ) (hq : q ≠ 0) (hq2 : q ^ 2 ≠ 1)
    (hu : ∀ i, u i ≠ 0) (hinj : Function.Injective u) :
    ¬ IsSemisimpleRing (H F r n q u) → ¬ IsSemisimpleRing (B F r n q u ε) := by sorry

end CycBMW.Semisimple
