-- Prove2me | Theorems.Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
-- name    : CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/e8e0b1c5-9141-5ca4-b2fa-f93c3dd0f1dd
-- title:
--   Strict bound |a|²<(p+1)²p^{k-2} for Hecke eigenvalues
-- statement:
--   Let $M$ be a natural number, nonzero, let $k$ be an integer, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$. Assume $g \neq 0$ and that $g$ has nebentypus $\varepsilon$, meaning that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau$ in the upper half-plane, $g(\gamma \cdot \tau) = \varepsilon(d)\,(c\tau + d)^k\, g(\tau)$, where $c$ and $d$ are the entries in positions $(1,0)$ and $(1,1)$ of $\gamma$, the former reduced mod $M$ in the argument of $\varepsilon$. Let $p$ be a prime not dividing $M$, and let $a \in \mathbb{C}$ satisfy the $T_p$-eigenvalue recursion on $q$-expansion coefficients: writing $a_n$ for the $n$-th coefficient of the $q$-expansion of $g$ of width $1$, one has, for every natural number $n$, $a_{pn} + \varepsilon(p)\,p^{\,k-1}\,a_{n/p} = a\,a_n$, where the second term is interpreted as $0$ unless $p \mid n$. The conclusion is the strict inequality $\lVert a \rVert^2 < (p+1)^2 p^{\,k-2}$ of real numbers, the exponent $k-2$ being an integer power.
--
--   This is the elementary operator-norm bound for the Hecke operator $T_p$ at a prime away from the level, with the case of equality excluded; it is much weaker than the Ramanujan–Petersson estimate but needs neither the Eichler–Shimura relation nor the Riemann hypothesis for curves over finite fields. In the present development it serves to rule out the degenerate eigenvalues $a$ with $a^2 = (p+1)^2\varepsilon(p)p^{k-2}$, and is invoked in the analysis of primitive forms, of Hecke eigenpackets and of Frobenius characteristic polynomials at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n)
      + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0)
        = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 < ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2) := by sorry
