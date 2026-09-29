-- Prove2me | Theorems.Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
-- name    : DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/cc71dc6d-ce89-53eb-8ca4-6880bedb8c76
-- title:
--   Eigencharacter with prescribed minimal prime kernel
-- statement:
--   Let $K$ be an algebraically closed field, $V$ a finite-dimensional $K$-vector space, and $T$ a commutative ring equipped with a $T$-module structure on $V$ whose action commutes with the $K$-action (so each $t \in T$ acts $K$-linearly) and which is faithful (an element of $T$ acting as zero on all of $V$ is zero); thus $T$ may be regarded as a commutative subring of $\operatorname{End}_K(V)$. Let $\mathfrak p$ be an ideal of $T$ belonging to $\operatorname{minimalPrimes} T$, i.e. a minimal element of the set of prime ideals of $T$ containing $\bot$. The assertion is that there exist a ring homomorphism $\chi : T \to K$ with $\ker \chi = \mathfrak p$ and a vector $x \in V$ such that $x \ne 0$, every $p \in \mathfrak p$ satisfies $p \cdot x = 0$, conversely every $r \in T$ with $r \cdot x = 0$ lies in $\mathfrak p$ (so the annihilator of $x$ in $T$ is exactly $\mathfrak p$), and $t \cdot x = \chi(t)\, x$ for all $t \in T$. No finiteness hypothesis is imposed on $T$ itself.
--
--   This is an abstract form of the statement, used for Hecke algebras in the study of weight-one forms by Deligne and Serre, that a minimal prime of a commutative ring acting faithfully on a finite-dimensional space is cut out by an eigencharacter admitting a common eigenvector. It is cited in the project by [`DeligneSerre.exists_eigencharacter_of_annihilator_le`](thm.html#DeligneSerre.exists_eigencharacter_of_annihilator_le), by [`DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr`](thm.html#DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr), and by [`Module.End.exists_common_eigenvector_of_commute`](thm.html#Module.End.exists_common_eigenvector_of_commute).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean

import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x := by sorry
