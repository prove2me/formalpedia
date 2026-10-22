-- Prove2me | Theorems.Thm_CycBMW_Semisimple_proposition_6_1
-- name    : CycBMW.Semisimple.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:41.487832+00:00
-- url     : https://prove2.me/theorems/831ca261-c761-4782-83fc-0cae3c3051ed
-- title:
--   Proposition 6.1 (restated: $\det G_{1,\emptyset}$ as the Hankel determinant $\det(\omega_{a+b})_{a,b\in N_r}$)
-- statement:
--   Let $F$ be a field, $r \ge 1$, $q, u_1,\dots,u_r \in F$ non-zero with $q^2 \ne 1$ and the $u_i$ pairwise distinct, $\varepsilon \in \{1,-1\}$, and let $\omega_a$ ($a \in \mathbb Z$) be the u-admissible parameters of Assumption 2.2. Let $N_r$ be the set (2.3) of $r$ consecutive integers and $\mathcal H = (\omega_{a+b})_{a,b \in N_r}$. Then $\det \mathcal H \ne 0$ if and only if
--
--   1. $u_iu_j - 1 \ne 0$ for all $1 \le i \ne j \le r$, and
--   2. $u_i \notin Q_{r,\varrho}$ for all $i$, where $Q_{r,\varrho} = \{-\varepsilon q, \varepsilon q^{-1}\}$ if $r$ is odd ($\varrho^{-1} = \varepsilon\prod_i u_i$) and $Q_{r,\varrho} = \{-q^\varepsilon, q^\varepsilon\}$ if $r$ is even ($\varrho^{-1} = \varepsilon q^{-\varepsilon}\prod_i u_i$).
--
--   $$\det\big(\omega_{a+b}\big)_{a,b\in N_r} \ne 0 \iff \Big(\forall i\ne j:\ u_iu_j \ne 1\Big) \wedge \Big(\forall i:\ u_i \notin Q_{r,\varrho}\Big).$$
--
--   In the paper the determinant is the Gram determinant $\det G_{1,\emptyset}$ of the cell module $\Delta(1,\emptyset)$, whose Gram matrix in the basis $E_1X_1^a$, $a \in N_r$, is $(\omega_{a+b})$ by relation g). This is the first of the determinant conditions that make up the semisimplicity criterion.
--
--   **Formalization Note** The statement is the paper's Proposition 6.1 with $\det G_{1,\emptyset}$ written as the Hankel determinant of the $\omega_a$ (the paper writes "$G_{1,\emptyset} \ne 0$" for $\det G_{1,\emptyset} \ne 0$). The standing assumption of §6 ($o(q^2)>n$ and Ariki's condition) concerns $n$ and does not enter this $n$-independent identity; it is omitted. The Lean index $a \in \{0,\dots,r-1\}$ stands for $a + \min N_r$.
-- source:
--   Rui and Si, The representation theory of cyclotomic BMW algebras, arXiv:0807.4149v1, p. 23, Proposition 6.1; p. 3, (2.3); p. 2, Definition 2.1 g)

import Mathlib
import Definitions.Def_CycBMW_Semisimple_Setting

namespace CycBMW.Semisimple

/-- Proposition 6.1, p. 23, restated: `det G_{1,∅}` is written as the Hankel determinant
`det (ω_{a+b})_{a,b ∈ N_r}`. -/
theorem proposition_6_1 {F : Type*} [Field F] (r : ℕ) (hr : 1 ≤ r)
    (q : F) (u : Fin r → F) (ε : ℤˣ) (hq : q ≠ 0) (hq2 : q ^ 2 ≠ 1)
    (hu : ∀ i, u i ≠ 0) (hinj : Function.Injective u) :
    (hankel r q u ε).det ≠ 0 ↔
      (∀ i j : Fin r, i ≠ j → u i * u j - 1 ≠ 0) ∧ ∀ i : Fin r, u i ∉ Qset r q ε := by sorry

end CycBMW.Semisimple
