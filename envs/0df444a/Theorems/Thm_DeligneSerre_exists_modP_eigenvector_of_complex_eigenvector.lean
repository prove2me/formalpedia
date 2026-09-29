-- Prove2me | Theorems.Thm_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector
-- name    : DeligneSerre.exists_modP_eigenvector_of_complex_eigenvector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/6c6b780b-eaa9-5961-aa4c-46b657f6f5d1
-- title:
--   Reduction of a common complex eigenvector modulo p
-- statement:
--   Fix a natural number $t$, an arbitrary index type $I$, and a family $A : I \to \mathrm{M}_t(\mathbb{Z})$ of $t \times t$ integer matrices indexed by $I$. Let $p$ be a prime, and let $\mathfrak{m}$ be a prime ideal of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ (the ring of all algebraic integers in $\mathbb{C}$) whose members include the image of $p$. Suppose given a family $\alpha : I \to \overline{\mathbb{Z}}$ of algebraic integers and a vector $v : \mathrm{Fin}\,t \to \mathbb{C}$ with $v \neq 0$ such that, for every index $i$, the matrix $A i$ with entries mapped into $\mathbb{C}$ satisfies $(A i) v = \alpha_i v$, i.e. $v$ is a common eigenvector of the family with eigenvalue $\alpha_i$ at $i$. Suppose further given integers $n : I \to \mathbb{Z}$ with $\alpha_i - n_i \in \mathfrak{m}$ for every $i$. The conclusion asserts the existence of a vector $m : \mathrm{Fin}\,t \to \mathbb{Z}/p$ with $m \neq 0$ such that, for every $i$, the matrix $A i$ reduced modulo $p$ satisfies $(A i) m = n_i m$ in $(\mathbb{Z}/p)^t$, where $n_i$ is taken modulo $p$. No commutativity of the family, and no finiteness of $I$, is assumed.
--
--   This is the reduction step in the Deligne–Serre argument passing from a complex eigenvector of a family of integral Hecke matrices to a nonzero eigenvector over $\mathbb{Z}/p$ with the prescribed integral eigenvalues. It is used in the construction of mod $p$ eigenclasses in parabolic cohomology and in the level-raising and newform arguments attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Matrix

theorem DeligneSerre.exists_modP_eigenvector_of_complex_eigenvector
    {t : ℕ} {I : Type*} (A : I → Matrix (Fin t) (Fin t) ℤ)
    {p : ℕ} [Fact p.Prime]
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (hmax : 𝔪.IsPrime)
    (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    {α : I → integralClosure ℤ ℂ} {v : Fin t → ℂ} (hv : v ≠ 0)
    (heig : ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec v = ((α i : ℂ) • v))
    {n : I → ℤ} (hcong : ∀ i, α i - (n i : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∃ m : Fin t → ZMod p, m ≠ 0 ∧
      ∀ i, ((A i).map (Int.cast : ℤ → ZMod p)).mulVec m = ((n i : ZMod p) • m) := by sorry
