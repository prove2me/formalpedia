-- Prove2me | Theorems.Thm_CycBMW_Semisimple_proposition_6_5_b
-- name    : CycBMW.Semisimple.proposition_6_5_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:50.190344+00:00
-- url     : https://prove2.me/theorems/9026d7ba-95b4-419c-885a-5c2e94eee849
-- title:
--   Proposition 6.5(b) (restated) — $\mathscr B_{r,n}$ is not semisimple if $\det(\omega_{a+b})_{a,b\in N_r} = 0$
-- statement:
--   Let $F$ be a field, $r \ge 2$, $n \ge 2$, $q, u_1,\dots,u_r \in F$ non-zero with $q^2 \ne 1$ and the $u_i$ pairwise distinct, $\varepsilon \in \{1,-1\}$, and u-admissible parameters as in Assumption 2.2. Assume the standing hypotheses of Propositions 6.1–6.5:
--
--   1. $o(q^2) > n$, i.e. $q^{2k} \ne 1$ for $1 \le k \le n$;
--   2. $|d| \ge n$ whenever $u_iu_j^{-1} = q^{2d}$ with $i \ne j$ and $d \in \mathbb Z$.
--
--   If the Hankel determinant $\det(\omega_{a+b})_{a,b \in N_r}$ (that is, $\det G_{1,\emptyset}$) vanishes, then
--   $$\mathscr B_{r,n} \text{ is not semisimple over } F.$$
--
--   Together with Proposition 6.1 this yields part (a) of the semisimplicity criterion under the standing hypotheses.
--
--   **Formalization Note** "Semisimple" is Mathlib's `IsSemisimpleRing`. $\det G_{1,\emptyset}$ is written as the Hankel determinant of the $\omega_a$, as in the restated Proposition 6.1. The paper's standing hypothesis reads "$|d| \ge n$ whenever $u_iu_j^{-1} - q^{2d} = 0$"; it is stated for $i < j$, which is equivalent to all $i \ne j$ (replace $d$ by $-d$) and excludes $i = j$, where $d = 0$ would make it unsatisfiable.
-- source:
--   Rui and Si, The representation theory of cyclotomic BMW algebras, arXiv:0807.4149v1, p. 23, Proposition 6.5(b) and the standing assumption of Propositions 6.1–6.5

import Mathlib
import Definitions.Def_CycBMW_Semisimple_Setting

namespace CycBMW.Semisimple

/-- Proposition 6.5(b), p. 23, restated with `det G_{1,∅}` as the Hankel determinant, under the
standing assumption of Propositions 6.1–6.5 (`o(q²) > n` and Ariki's condition). -/
theorem proposition_6_5_b {F : Type*} [Field F] (r n : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n)
    (q : F) (u : Fin r → F) (ε : ℤˣ) (hq : q ≠ 0) (hq2 : q ^ 2 ≠ 1)
    (hu : ∀ i, u i ≠ 0) (hinj : Function.Injective u)
    (hord : OrderGt q n) (hariki : ArikiCond q u n)
    (hdet : (hankel r q u ε).det = 0) :
    ¬ IsSemisimpleRing (B F r n q u ε) := by sorry

end CycBMW.Semisimple
