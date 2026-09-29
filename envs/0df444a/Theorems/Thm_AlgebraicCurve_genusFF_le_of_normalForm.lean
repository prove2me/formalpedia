-- Prove2me | Theorems.Thm_AlgebraicCurve_genusFF_le_of_normalForm
-- name    : AlgebraicCurve.genusFF_le_of_normalForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/942950b9-dbe4-5197-b51b-9e4c75675ce8
-- title:
--   Genus bound for a function field in normal form
-- statement:
--   Let $L$ be an algebraically closed field and $F'$ a field extension of $L$, let $n$ be a natural number, and let $y \in F'$ be transcendental over $L$ and such that $F'$ is finite-dimensional over the intermediate field $L(y) =$ `IntermediateField.adjoin L {y}` with $[F' : L(y)] = n+1$. Suppose given elements $s_0,\dots,s_n \in F'$ and weights $d_0,\dots,d_n \in \mathbb{N}$ with $s_0 = 1$ and $d_0 = 0$, with $d_i \in \{1,2\}$ for every $i \neq 0$, together with polynomials $c_{ijk} \in L[X]$ such that the multiplication table $s_i s_j = \sum_k c_{ijk}(y)\, s_k$ holds for all $i,j$ (evaluation of $c_{ijk}$ at $y$ via the $L$-algebra structure of $F'$), such that $\deg c_{ijk} \le d_i + d_j - d_k$ (truncated subtraction of natural numbers) whenever $i \neq 0$ and $j \neq 0$, and such that $s_0,\dots,s_n$ are linearly independent over $L[y]$ in the sense that $\sum_i e_i(y)\, s_i = 0$ for $e : \mathrm{Fin}(n+1) \to L[X]$ forces $e = 0$. Then $g + n \le \sum_i d_i$, where $g =$ `genusFF L F'` is the $L$-dimension of $H^1$ of the zero divisor of $F'/L$, a divisor being a finitely supported $\mathbb{Z}$-valued function on the places of $F'$ over $L$.
--
--   This is the inequality "genus of the function field $\le$ arithmetic genus of the normal form", the latter being $\sum_i d_i - n = \#\{i : d_i = 2\}$ for a normal form with weights $d_i$; equivalently, the genus of the curve with function field $F'$ is bounded by $h^1$ of $\bigoplus_i \mathcal{O}_{\mathbb{P}^1}(-d_i)$. It is used, via [`AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder`](thm.html#AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder), to control the genus of the generic fibre of a lifted normal-form order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genusFF_le_of_normalForm.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

universe u v

theorem AlgebraicCurve.genusFF_le_of_normalForm
    {L : Type u} {F' : Type v} [Field L] [IsAlgClosed L] [Field F'] [Algebra L F']
    (n : ℕ) (y : F') (hy : Transcendental L y)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({y} : Set F')) F')
    (hdegF : Module.finrank (IntermediateField.adjoin L ({y} : Set F')) F' = n + 1)
    (s : Fin (n + 1) → F') (d : Fin (n + 1) → ℕ) (hs0 : s 0 = 1) (hd0 : d 0 = 0)
    (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (c : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → L[X])
    (hmul : ∀ i j, s i * s j = ∑ k, Polynomial.aeval y (c i j k) * s k)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → (c i j k).natDegree ≤ d i + d j - d k)
    (hind : ∀ e : Fin (n + 1) → L[X], ∑ i, Polynomial.aeval y (e i) * s i = 0 → e = 0) :
    genusFF L F' + n ≤ ∑ i, d i := by sorry
