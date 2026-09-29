-- Prove2me | Theorems.Thm_Deformation_exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero
-- name    : Deformation.exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/77147c4c-a0a3-57a8-8dce-fa66ae5accee
-- title:
--   pⁿ-torsion abelian groups as 𝒪-modules
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime number such that the image of $p$ in $\mathcal O$ is a non-zero-divisor, and suppose $\mathcal O$ is equipped with an algebra structure over $\mathbf Z/p$ whose structure morphism $\mathcal O \to \mathbf Z/p$ has kernel exactly the principal ideal $(p)$ of $\mathcal O$. Let $M$ be an additive abelian group and $n$ a natural number such that $(p^n) \cdot x = 0$ for every $x \in M$, the action being the integer scalar action on $M$. The assertion is that there exists an $\mathcal O$-module structure on $M$ (on top of its given additive group structure) with two properties: first, for every integer $m$ and every $x \in M$, the action of the image of $m$ in $\mathcal O$ on $x$ agrees with the integer scalar action $m \cdot x$; second, every $a \in \mathcal O$ acts on all of $M$ through some single integer, i.e. for each $a$ there is $m \in \mathbf Z$ with $a \cdot x = m \cdot x$ for all $x \in M$. The module structure is produced as existential data, not as an instance.
--
--   This is the elementary bridge from $\mathbf Z$-module structures to $\mathcal O$-module structures on $p^n$-torsion groups, valid because the hypotheses force $\mathbf Z/p^n \to \mathcal O/p^n\mathcal O$ to be an isomorphism; it allows groups such as Dieudonné-type modules or Cartier duals, constructed purely additively, to be regarded as $\mathcal O$-modules with all additive maps automatically $\mathcal O$-linear. It is used in the construction of $p$-divisible towers with prescribed kernels in the deformation-theoretic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (M : Type v) [AddCommGroup M] (n : ℕ) (hM : ∀ x : M, (p ^ n : ℤ) • x = 0) :
    ∃ inst : Module 𝓞 M,
      (∀ (m : ℤ) (x : M), @HSMul.hSMul 𝓞 M M (@instHSMul 𝓞 M inst.toSMul) (m : 𝓞) x = m • x) ∧
      (∀ a : 𝓞, ∃ m : ℤ, ∀ x : M, @HSMul.hSMul 𝓞 M M (@instHSMul 𝓞 M inst.toSMul) a x = m • x) := by sorry
