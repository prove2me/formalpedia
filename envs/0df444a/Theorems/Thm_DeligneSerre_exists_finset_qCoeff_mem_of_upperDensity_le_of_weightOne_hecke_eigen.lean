-- Prove2me | Theorems.Thm_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
-- name    : DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/eb8058d4-b3d0-54d9-8756-bfda385a8e54
-- title:
--   Deligne–Serre: weight-one eigenvalues lie in an order, few exceptions
-- statement:
--   Let $N$ be a nonzero natural number, $\varepsilon$ a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and $f$ a cusp form of weight $1$ for $\Gamma_1(N)$; write $a_n = \mathrm{qCoeff}\, f\, n$ for the $n$-th coefficient of the $q$-expansion of $f$ at $\infty$ (the expansion of width $1$). Assume $a_1 = 1$ and that for every prime $p \nmid N$ and every natural number $n$ one has $a_{pn} + \varepsilon(p)\,a_{n/p}\,[p \mid n] = a_p a_n$, where the second term is interpreted as $0$ when $p \nmid n$ and $n/p$ is natural division. The conclusion asserts the existence of a $\mathbb{Z}$-subalgebra $R \subseteq \mathbb{C}$ that is finite as a $\mathbb{Z}$-module and contains $a_p$ for every prime $p \nmid N$, and, for every real $\eta > 0$, of a finite set $Y$ of complex numbers and a set $X$ of natural numbers such that: for every $\delta > 0$ there is $s_0 > 1$ with $\sum_{p \in X,\ p \text{ prime}} p^{-s} \le (\eta + \delta)\log\bigl(1/(s-1)\bigr)$ for all $1 < s < s_0$ (the sum being the unconditional infinite sum over the subtype of primes lying in $X$); and $a_p \in Y$ for every prime $p \nmid N$ with $p \notin X$.
--
--   This is Proposition 5.5 of Deligne–Serre, combined with the integrality statement of their Proposition 2.7: the Hecke eigenvalues of a normalised weight-one eigenform generate an order in a number field, and outside a set of primes of upper Dirichlet density at most $\eta$ (in the explicit $\log(1/(s-1))$ form above) they take only finitely many values. It is the input for the construction of the associated two-dimensional Galois representation in [`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`](thm.html#DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R) ∧
      ∀ η : ℝ, 0 < η → ∃ (Y : Finset ℂ) (X : Set ℕ),
        (∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
          ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
            (η + δ) * Real.log (1 / (s - 1))) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ X → ModularFormClass.qCoeff f p ∈ Y := by sorry
