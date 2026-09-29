-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_lemma2
-- name    : BealeConvexMin.QuadSimplex.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:33:37.639215+00:00
-- url     : https://prove2.me/theorems/da0c0a1c-baff-4720-b958-b13f6136cbd5
-- title:
--   Lemma 2 — a decoupled variable stays decoupled when a free variable enters
-- statement:
--   Let $(c_{kl})_{k,l=0}^{N}$ have $c_{pp}\neq0$, let the new nonbasic variable be the free variable $u_r=c_{p0}+\sum_{l\ge1}c_{pl}z_l$ of (3.2) (so $d_l=c_{pl}$ in (3.3)), and let $l\neq p$ be a slot with
--   $$c_{kl}=c_{lk}=0\qquad\text{for all }k\neq l .$$
--   Then $e_l=0$, and the property persists in the new matrix:
--   $$c''_{kl}=c''_{lk}=0\qquad\text{for all }k\neq l .$$
--
--   Together with Lemma 1 this shows that a free variable that has entered with no linear or cross terms keeps that property until some restricted variable becomes nonbasic, which is the second half of Beale's termination argument.
--
--   **Formalization Note** The index $0$ is included in "$k\neq l$". The hypothesis $l\neq p$ is implicit in the paper ($z_l$ is a variable that stays nonbasic) and is necessary, since $e_p$ is the coefficient of the new variable. The hypothesis $c_{pp}\neq0$ is the paper's $d_{qp}\neq0$.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), Lemma 2

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177, Lemma 2. Let the new nonbasic variable be the free variable of (3.2)
(coefficients `d = c p`, row `p` of `c`, with `c_pp ≠ 0`), and let `l ≠ p` be a slot whose row and
column of `(c_kl)` vanish off the diagonal: `c_kl = c_lk = 0` for all `k ≠ l` (index `0` included).
Then `e_l = 0`, and the new matrix keeps the property: `c''_kl = c''_lk = 0` for all `k ≠ l`. -/
theorem lemma2 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hp : c p p ≠ 0) (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotE (c p) p l = 0 ∧
    ∀ k, k ≠ l → pivotC c p (c p) k l = 0 ∧ pivotC c p (c p) l k = 0 := by sorry

end BealeConvexMin.QuadSimplex
