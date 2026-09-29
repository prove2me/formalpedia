-- Prove2me | Theorems.Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen
-- name    : CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/5da33dff-ce5a-5c85-bf6a-6c0ab89a9e3b
-- title:
--   Hecke eigen-relations produce a nebentypus character
-- statement:
--   Let $N \ge 1$ be an integer and $k$ an integer, let $f$ be a cusp form of weight $k$ for $\Gamma_1(N)$ with $f \neq 0$, and let $\chi : \mathbb{N} \to \mathbb{C}$ be an arbitrary function (no multiplicativity or character property is assumed). Write $a_n =$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of $f$ of width $1$. Assume that for every prime $p$ not dividing $N$ there exists $\lambda \in \mathbb{C}$ with
--   $$a_{pn} + \chi(p)\cdot\bigl(\text{$a_{n/p}$ if $p \mid n$, else $0$}\bigr) = \lambda\, a_n \qquad \text{for every } n \in \mathbb{N}$$
--   (the index $n$ ranges over all natural numbers, $n = 0$ included). Then there exists a Dirichlet character $\varepsilon$ modulo $N$ with values in $\mathbb{C}$ such that, first, $f$ has nebentypus $\varepsilon$ in the sense that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(N)$ and every $\tau$ in the upper half-plane,
--   $$f(\gamma \cdot \tau) = \varepsilon(\gamma_{11} \bmod N)\,\bigl(\gamma_{10}\tau + \gamma_{11}\bigr)^{k} f(\tau),$$
--   and, second, $\varepsilon(p)\, p^{\,k-1} = \chi(p)$ for every prime $p$ not dividing $N$.
--
--   This is the standard recognition statement that a nonzero cusp form on $\Gamma_1(N)$ whose $q$-coefficients satisfy the $T_p$ recursion with arbitrary multipliers $\chi(p)$ at all primes $p \nmid N$ automatically carries a nebentypus character, the multipliers being $\varepsilon(p)p^{k-1}$. It is used in the treatment of primitive forms, for instance by [`CuspForm.IsPrimitiveForm.heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level`](thm.html#CuspForm.IsPrimitiveForm.heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level) and by the results attaching Hecke-algebra homomorphisms to such forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (χ : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            χ p * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam * ModularFormClass.qCoeff f n) :
    ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε f ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N → ε (p : ZMod N) * (p : ℂ) ^ (k - 1) = χ p := by sorry
