-- Prove2me | Theorems.Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
-- name    : AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/88670112-78a9-5e55-a02d-87fb32b926a1
-- title:
--   Threads of an adic system as a finite module over ̂ B
-- statement:
--   Let $B$ be a commutative ring and $I \subseteq B$ a finitely generated ideal. Let $(M_n)_{n \ge 0}$ be a family of $B$-modules, indexed by the naturals and living in a fixed universe, equipped with $B$-linear transition maps $t_n : M_{n+1} \to M_n$, and assume that each $t_n$ is surjective, that $\ker t_n = I^{n+1} \cdot \top$, the submodule $I^{n+1}M_{n+1}$ of $M_{n+1}$, for every $n$, and that $M_0$ is a finite $B$-module. The assertion is the existence of a type $L$ in the same universe as the $M_n$, carrying an additive commutative group structure, a $B$-module structure and a module structure over the $I$-adic completion `AdicCompletion I B` that is compatible with the $B$-action via the structure map (a scalar tower), such that $L$ is finite as a module over `AdicCompletion I B`, together with $B$-linear maps $\mathrm{pr}_n : L \to M_n$ satisfying: $t_n(\mathrm{pr}_{n+1}(x)) = \mathrm{pr}_n(x)$ for all $n$ and $x \in L$; an element of $L$ killed by every $\mathrm{pr}_n$ is zero; every compatible family $(m_n)_n$ with $t_n(m_{n+1}) = m_n$ is of the form $(\mathrm{pr}_n(x))_n$ for some $x \in L$; each $\mathrm{pr}_n$ is surjective; and $\ker \mathrm{pr}_n = I^{n+1} \cdot \top = I^{n+1}L$ for every $n$.
--
--   The conclusion says that the inverse limit of an adic system of $B$-modules with surjective transitions and kernels exactly $I^{n+1}M_{n+1}$ is a finite module over the $I$-adic completion of $B$, with the given levels recovered as its truncations $L/I^{n+1}L$; the existential packaging avoids naming the limit construction. It is used in the treatment of $\mathcal{O}$-module presheaves, where threads of such a system must be produced over a completed base, and it rests on [`IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top`](thm.html#IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top) applied over the complete ring `AdicCompletion I B`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I.FG)
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module B (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[B] M n)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) = I ^ (n + 1) • (⊤ : Submodule B (M (n + 1))))
    (hfin : Module.Finite B (M 0)) :
    ∃ (L : Type v) (_ : AddCommGroup L) (_ : Module B L) (_ : Module (AdicCompletion I B) L)
      (_ : IsScalarTower B (AdicCompletion I B) L) (_ : Module.Finite (AdicCompletion I B) L)
      (pr : ∀ n : ℕ, L →ₗ[B] M n),
      (∀ (n : ℕ) (x : L), t n (pr (n + 1) x) = pr n x) ∧
      (∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0) ∧
      (∀ m : ∀ n : ℕ, M n, (∀ n : ℕ, t n (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n) ∧
      (∀ n : ℕ, Function.Surjective (pr n)) ∧
      (∀ n : ℕ, LinearMap.ker (pr n) = I ^ (n + 1) • (⊤ : Submodule B L)) := by sorry
