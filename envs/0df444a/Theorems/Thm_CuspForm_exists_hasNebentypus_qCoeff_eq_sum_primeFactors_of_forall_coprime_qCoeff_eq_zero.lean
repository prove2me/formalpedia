-- Prove2me | Theorems.Thm_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
-- name    : CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/c9a6b8b3-eb50-51af-b7ed-eb67b05ff83d
-- title:
--   Atkin–Lehner level lowering along a nebentypus
-- statement:
--   Let $N \geq 1$ and $K \neq 0$ be natural numbers, let $k$ be an integer, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and let $f$ be a cusp form of weight $k$ on $\Gamma_1(N)$ which has nebentypus $\varepsilon$, meaning that for every $\gamma \in \Gamma_0(N)$ and every $\tau$ in the upper half-plane one has $f(\gamma \cdot \tau) = \varepsilon(\gamma_{11} \bmod N) \, (\gamma_{10}\tau + \gamma_{11})^{k} f(\tau)$. Assume that the $q$-expansion coefficients $a_n(f)$ of $f$ (the coefficients of `qExpansion 1 f`) vanish for every $n$ coprime to $K$. Then there is a family $g$ assigning to each natural number $p$ a cusp form $g_p$ of weight $k$ on $\Gamma_1(N/p)$ such that: for every prime factor $p$ of $N$, either $g_p = 0$, or there is a Dirichlet character $\varepsilon_p$ modulo $N/p$ whose change of level along $(N/p) \mid N$ equals $\varepsilon$ and for which $g_p$ has nebentypus $\varepsilon_p$; and for every natural number $n$, $a_n(f) = \sum_{p \mid N \text{ prime}} [\,p \mid n\,]\, a_{n/p}(g_p)$, i.e. $f(\tau) = \sum_{p \mid N} g_p(p\tau)$ on $q$-coefficients. No condition is imposed on $g_p$ for $p$ outside the prime factors of $N$.
--
--   This is the refinement along the eigenspaces of the diamond operators of the theorem of Atkin and Lehner, in the form used by Li: a cusp form of level $N$ and nebentypus $\varepsilon$ whose coefficients vanish at all indices prime to $K$ is a sum of $p$-stretches $g_p(p\tau)$ of forms of level $N/p$, each nonzero $g_p$ again carrying a nebentypus inducing $\varepsilon$. It feeds the theory of primitive forms in this development, being used for the identification of the level and coefficients of a primitive form, for the rigidity statement on Hecke eigenforms, and for the decomposition of a form with nebentypus into primitive forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hε : CuspForm.HasNebentypus ε f)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (p : ℕ) → CuspForm (Gamma1 (N / p)) k,
      (∀ (p : ℕ) (hp : p ∈ N.primeFactors), g p = 0 ∨
        ∃ εp : DirichletCharacter ℂ (N / p),
          DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
          CuspForm.HasNebentypus εp (g p)) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff f n =
        ∑ p ∈ N.primeFactors, if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0 := by sorry
