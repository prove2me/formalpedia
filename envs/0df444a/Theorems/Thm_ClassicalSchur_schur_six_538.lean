-- Prove2me | Theorems.Thm_ClassicalSchur_schur_six_538
-- name    : ClassicalSchur.schur_six_538
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-11-04T05:39:50.291466+00:00
-- url     : https://prove2.me/theorems/05b7c0f2-3f34-4ee4-89e4-381a700752d3
-- title:
--   A Schur colouring of $[1,538]$ with six colours, so $S(6)\ge 538$
-- statement:
--   The integers $1,\dots,538$ have a colouring with six colours such that, for all positive integers $x$ and $y$ with $x+y\le 538$, the integers $x$, $y$ and $x+y$ do not all have one colour. The case $x=y$ is included. So $\{1,\dots,538\}$ is the union of six sum-free sets.
--
--   The Schur number $S(k)$ is the largest $n$ such that $\{1,\dots,n\}$ is the union of $k$ sum-free sets. By this definition, the theorem gives $S(6)\ge 538$. The formal statement does not define $S(k)$, so this last step is outside Lean.
--
--   In the formal statement the colouring is a function $c:\mathbb{N}\to\mathrm{Fin}\,6$. Only its values on $1,\dots,538$ matter, and the statement does not require that each colour is used.
-- source:
--   A. McKenna, "The sixth Schur number is at least 538", Zenodo preprint (2026), https://doi.org/10.5281/zenodo.23937655, Theorem 1. Also aiXiv 2611.00368, https://aixiv.online/abs/2611.00368. Lean source: https://github.com/mysticflounder/schur-538/blob/c3306693e01496162241bb7630ff2f19bd1482b7/lean/SchurSix538.lean (theorem schur_six_538).

namespace ClassicalSchur
theorem schur_six_538 : ∃ c : Nat → Fin 6, ∀ x y : Nat, 1 ≤ x → 1 ≤ y → x + y ≤ 538 → ¬ (c x = c y ∧ c y = c (x + y)) := by sorry
end ClassicalSchur
