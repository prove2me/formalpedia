-- Prove2me | Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus
-- name    : CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/1302dccb-1637-5ef9-9726-b5fe3723eefc
-- title:
--   Newform decomposition of cusp forms with nebentypus
-- statement:
--   Let $N \ge 1$ and $k \in \mathbb{Z}$, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and let $f$ be a cusp form of weight $k$ on $\Gamma_1(N)$ satisfying [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) for $\varepsilon$, i.e. $f(\gamma\tau) = \varepsilon(\gamma_{11})\,(\gamma_{10}\tau + \gamma_{11})^{k} f(\tau)$ for all $\gamma \in \Gamma_0(N)$ and all $\tau$ in the upper half-plane. Then there exist an $n \in \mathbb{N}$, natural numbers $M_i, d_i$ for $i \in \{1,\dots,n\}$ with $M_i d_i \mid N$, Dirichlet characters $\varepsilon_i$ modulo $M_i$, cusp forms $g_i$ of weight $k$ on $\Gamma_1(M_i)$, and scalars $c_i \in \mathbb{C}$, such that each $g_i$ is a primitive form with character $\varepsilon_i$ in the sense of [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38) — its first $q$-expansion coefficient is $1$, it satisfies $b_{pm} + \varepsilon_i(p)p^{k-1}[p \mid m]b_{m/p} = b_p b_m$ for all primes $p \nmid M_i$ and all $m$, it satisfies $b_{\ell m} = b_\ell b_m$ for all primes $\ell \mid M_i$ and all $m$, it has nebentypus $\varepsilon_i$, and for no proper divisor $M' \mid M_i$ does the eigenpacket $(b_p, \varepsilon_i(p))$ occur, in the sense of `EigenpacketOccursAt`, in a nonzero weight-$k$ cusp form on $\Gamma_1(M')$ with some character modulo $M'$ away from a finite set of primes — and such that $\varepsilon_i$ pushed forward to level $N$ is $\varepsilon$, while the $q$-expansion coefficients satisfy $a_m(f) = \sum_{i} c_i\,[d_i \mid m]\,b_{m/d_i}(g_i)$ for every $m \in \mathbb{N}$. Here the coefficients are those of [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19), the $q$-expansion with respect to period $1$.
--
--   This is the Atkin–Lehner–Li decomposition of the space of weight-$k$ cusp forms on $\Gamma_1(N)$ with fixed nebentypus into old and new parts, in the coefficientwise form $a_m(f) = \sum_i c_i b_{m/d_i}(g_i)$, equivalently $f(\tau) = \sum_i c_i g_i(d_i\tau)$ with each $g_i$ primitive of level $M_i$ and $M_i d_i \mid N$. It is used in the level-lowering part of the argument, where eigenpackets occurring at a divisor level must be realised by primitive forms of that level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus ε f) :
    ∃ (n : ℕ) (M d : Fin n → ℕ) (hM : ∀ i, M i * d i ∣ N)
      (εM : (i : Fin n) → DirichletCharacter ℂ (M i))
      (g : (i : Fin n) → CuspForm (Gamma1 (M i)) k) (c : Fin n → ℂ),
      (∀ i, CuspForm.IsPrimitiveForm (εM i) (g i) ∧
        DirichletCharacter.changeLevel (dvd_of_mul_right_dvd (hM i)) (εM i) = ε) ∧
      ∀ m : ℕ, ModularFormClass.qCoeff f m =
        ∑ i, c i * (if d i ∣ m then ModularFormClass.qCoeff (g i) (m / d i) else 0) := by sorry
