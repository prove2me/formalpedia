-- Prove2me | Theorems.Thm_DeligneSerre_exists_eigencharacter_of_annihilator_le
-- name    : DeligneSerre.exists_eigencharacter_of_annihilator_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/ac4d98cf-c8df-5d87-a4df-9e4f5d1aaed7
-- title:
--   Eigencharacter over ℤ̄ lifting a maximal ideal in the support
-- statement:
--   Let $V$ be an additive commutative group carrying a $\mathbb{C}$-module structure with $V$ finite-dimensional over $\mathbb{C}$, and let $T$ be a commutative ring acting on $V$ (a $T$-module structure on $V$) whose action commutes with the scalar action of $\mathbb{C}$, and which is finite as a $\mathbb{Z}$-module. Let $\mathfrak{m}$ be a maximal ideal of $T$ such that the annihilator $\operatorname{Ann}_T(V)$ (the ideal of $t \in T$ killing every vector of $V$) is contained in $\mathfrak{m}$; that is, $\mathfrak{m}$ lies in the support of $V$. The conclusion asserts the existence of a ring homomorphism $\chi : T \to \overline{\mathbb{Z}}$, where $\overline{\mathbb{Z}}$ denotes `integralClosure ℤ ℂ`, the ring of algebraic integers inside $\mathbb{C}$, together with a maximal ideal $\mathfrak{m}'$ of $\overline{\mathbb{Z}}$ whose preimage $\chi^{-1}(\mathfrak{m}')$ equals $\mathfrak{m}$, and a nonzero vector $x \in V$ which is a simultaneous eigenvector for the whole of $T$ with eigenvalues given by $\chi$: for every $t \in T$ one has $t \cdot x = \chi(t) \cdot x$, the scalar being the image of $\chi(t)$ in $\mathbb{C}$.
--
--   This is the linear-algebra core of the Deligne–Serre lifting argument in abstract form: a residual eigensystem $T \to T/\mathfrak{m}$ occurring in the support of a finite-dimensional complex representation of $T$ is the reduction, at a prime of the algebraic integers, of the eigencharacter of an honest eigenvector in $V$. It is used in the construction of complex Hecke eigenvectors from maximal ideals of Hecke algebras, and from there in producing Galois representations over finite fields whose traces match the Hecke action modulo $\mathfrak{m}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_eigencharacter_of_annihilator_le.lean

import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem DeligneSerre.exists_eigencharacter_of_annihilator_le
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T ℂ V] [Module.Finite ℤ T]
    (𝔪 : Ideal T) [h𝔪 : 𝔪.IsMaximal] (hsupp : Module.annihilator T V ≤ 𝔪) :
    ∃ (χ : T →+* integralClosure ℤ ℂ) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      𝔪'.IsMaximal ∧ 𝔪'.comap χ = 𝔪 ∧
      ∃ x : V, x ≠ 0 ∧ ∀ t : T, t • x = ((χ t : integralClosure ℤ ℂ) : ℂ) • x := by sorry
