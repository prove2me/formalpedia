-- Prove2me | Theorems.Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
-- name    : CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/81eee6d3-7504-5d39-9d21-6adcea5f50b0
-- title:
--   Conjugate Hecke eigenvalue equals ε(p)⁻¹λ
-- statement:
--   Let $M\ge 1$ be a natural number, $k$ an integer, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and $g$ a cusp form of weight $k$ for $\Gamma_1(M)$ with $g\neq 0$. Assume $g$ has nebentypus $\varepsilon$ in the sense that for every $\gamma\in SL_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau$ in the upper half-plane, $g(\gamma\cdot\tau)=\varepsilon(\gamma_{11}\bmod M)\,\bigl((\gamma_{10}\tau+\gamma_{11})^{k}\,g(\tau)\bigr)$, where the entries are taken from the bottom row of $\gamma$. Let $p$ be a prime with $p\nmid M$ and let $\lambda\in\mathbb{C}$. Write $b_n$ for the $n$-th coefficient of the $q$-expansion of $g$ of width $1$ (the project's `qCoeff`). Suppose the $T_p$-eigenrelation holds coefficientwise: for every $n\in\mathbb{N}$,
--   $$b_{pn}+\varepsilon(p)\,p^{\,k-1}\cdot\bigl(\text{$b_{n/p}$ if $p\mid n$, else $0$}\bigr)=\lambda\, b_n.$$
--   Then $\overline{\lambda}=\varepsilon^{-1}(p)\,\lambda$, the inverse being taken in the group of Dirichlet characters modulo $M$.
--
--   This is the classical statement that the Hecke eigenvalues of a nonzero form in $S_k(M,\varepsilon)$ at primes $p\nmid M$ satisfy $\overline{\lambda}=\bar\varepsilon(p)\lambda$, a consequence of the adjointness $T_p^{*}=\langle p\rangle^{-1}T_p$ for the Petersson product; the $T_p$-eigenrelation is imposed here directly on the $q$-expansion coefficients rather than through a Hecke operator. It feeds the construction of the Hecke eigenvalue homomorphisms attached to eigenforms and the subsequent analysis of primitive forms and their associated Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (lam : ℂ)
    (heig : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
      lam * ModularFormClass.qCoeff g n) :
    starRingEnd ℂ lam = ε⁻¹ (p : ZMod M) * lam := by sorry
