-- Prove2me | Theorems.Thm_CycBMW_Semisimple_semisimplicity_criterion
-- name    : CycBMW.Semisimple.semisimplicity_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:59.485989+00:00
-- url     : https://prove2.me/theorems/a801e666-b751-4718-9e5a-2d2ab44ab180
-- title:
--   Theorem 6.8 — semisimplicity criterion for the cyclotomic Birman–Wenzl algebra $\mathscr B_{r,n}$ ($n = 3$: necessity)
-- statement:
--   Let $F$ be a field, $n \ge 2$ and $r \ge 2$, let $q, u_1,\dots,u_r \in F$ be non-zero with $q - q^{-1} \ne 0$ and the $u_i$ pairwise distinct, let $\varepsilon \in \{1,-1\}$, and let $\mathscr B_{r,n}$ be the cyclotomic Birman–Wenzl algebra over $F$ with the u-admissible parameters of Assumption 2.2 ($\varrho^{-1} = \varepsilon\prod u_i$ for odd $r$, $\varrho^{-1} = \varepsilon q^{-\varepsilon}\prod u_i$ for even $r$).
--
--   **(a)** If $u_i - u_j^{-1} = 0$ for some $i \ne j$, or $u_i \in Q_{r,\varrho}$ for some $i$, then $\mathscr B_{r,n}$ is not semisimple.
--
--   **(b)** Assume $u_i - u_j^{-1} \ne 0$ for all $i \ne j$ and $u_i \notin Q_{r,\varrho}$ for all $i$.
--
--   1. $\mathscr B_{r,2}$ is semisimple if and only if $o(q^2) > 2$ and $|d| \ge 2$ whenever $u_iu_j^{-1} = q^{2d}$ for some $1 \le i < j \le r$ and $d \in \mathbb Z$.
--   2. For $n \ge 4$, $\mathscr B_{r,n}$ is semisimple if and only if
--      (a) $o(q^2) > n$; (b) $|d| \ge n$ whenever $u_iu_j^{-1} = q^{2d}$, $1 \le i < j \le r$, $d \in \mathbb Z$; (c) $u_i \notin S_{r,\varrho}$ for all $i$; (d) $u_iu_j \notin \bigcup_{k=3}^n\{q^{4-2k}, q^{2k-4}\}$ for all $i \ne j$.
--      $$\mathscr B_{r,n}\ \text{semisimple} \iff (a)\wedge(b)\wedge(c)\wedge(d).$$
--   3. For $n = 3$: if $\mathscr B_{r,3}$ is semisimple, then (a)–(d) hold with $n = 3$.
--
--   This is the main theorem of the paper: an explicit criterion, in terms of the parameters alone, for the cyclotomic Birman–Wenzl algebra to be semisimple; for $r = 1$ it was proved earlier for the Birman–Murakami–Wenzl algebra.
--
--   **Formalization Note** "Semisimple" is Mathlib's `IsSemisimpleRing`; $o(q^2) > n$ is "$q^{2k} \ne 1$ for $1 \le k \le n$". The sets $Q_{r,\varrho}$, $S_{r,\varrho}$ are those of (6.6)–(6.7), computed from $\varepsilon$. Two narrowings relative to the page: the $u_i$ are pairwise distinct (Assumption 2.2(1) divides by $u_i - u_j$), and for $n = 3$ only necessity is stated, because Proposition 6.2 and Lemma 6.3, on which sufficiency rests, give contradictory conditions for the same cell module at $n = 3$.
-- source:
--   Rui and Si, The representation theory of cyclotomic BMW algebras, arXiv:0807.4149v1, pp. 24–25, Theorem 6.8; p. 24, (6.6)–(6.7)

import Mathlib
import Definitions.Def_CycBMW_Semisimple_Setting

namespace CycBMW.Semisimple

/-- Theorem 6.8, pp. 24–25 (with `n = 3` stated as necessity only). -/
theorem semisimplicity_criterion {F : Type*} [Field F] (r n : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n)
    (q : F) (u : Fin r → F) (ε : ℤˣ) (hq : q ≠ 0) (hq2 : q ^ 2 ≠ 1)
    (hu : ∀ i, u i ≠ 0) (hinj : Function.Injective u) :
    -- (a)
    (((∃ i j : Fin r, i ≠ j ∧ u i - (u j)⁻¹ = 0) ∨ (∃ i : Fin r, u i ∈ Qset r q ε)) →
      ¬ IsSemisimpleRing (B F r n q u ε)) ∧
    -- (b)
    ((∀ i j : Fin r, i ≠ j → u i - (u j)⁻¹ ≠ 0) → (∀ i : Fin r, u i ∉ Qset r q ε) →
      -- (b)(1)
      (n = 2 → (IsSemisimpleRing (B F r n q u ε) ↔ OrderGt q 2 ∧ ArikiCond q u 2)) ∧
      -- (b)(2), n ≥ 4
      (4 ≤ n → (IsSemisimpleRing (B F r n q u ε) ↔
        OrderGt q n ∧ ArikiCond q u n ∧ (∀ i : Fin r, u i ∉ Sset r n q ε) ∧
          ∀ i j : Fin r, i ≠ j → u i * u j ∉ Dset n q)) ∧
      -- (b)(2), n = 3, necessity
      (n = 3 → IsSemisimpleRing (B F r n q u ε) →
        OrderGt q n ∧ ArikiCond q u n ∧ (∀ i : Fin r, u i ∉ Sset r n q ε) ∧
          ∀ i j : Fin r, i ≠ j → u i * u j ∉ Dset n q)) := by sorry

end CycBMW.Semisimple
