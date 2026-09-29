-- Prove2me | Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
-- name    : CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/0ea0ec70-e24f-5264-bce6-6aa9b0bc9482
-- title:
--   Existence of an attached primitive form for Tₚ-eigenvalues, p∤ N
-- statement:
--   Let $N\ge 1$ (as a natural number with `NeZero`), let $k$ be an integer, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and let $f$ be a nonzero cusp form of weight $k$ on $\Gamma_1(N)$ satisfying [`CuspForm.HasNebentypus ε f`](def/CuspForm_PrimitiveFormGamma1.html#L13), i.e. $f(\gamma\tau)=\varepsilon(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^{k}f(\tau)$ for all $\gamma\in\Gamma_0(N)$ and all $\tau$ in the upper half-plane. Write $a_n=$ `qCoeff f n`, the $n$-th coefficient of the $q$-expansion of width $1$. Let $\lambda:\mathbb{N}\to\mathbb{C}$ be such that for every prime $p\nmid N$ and every $n\ge 0$ one has $a_{pn}+\varepsilon(p)p^{k-1}a_{n/p}[p\mid n]=\lambda(p)a_n$ (no normalisation of $a_1$ is assumed). The conclusion asserts the existence of $M\ge 1$ dividing $N$, a Dirichlet character $\varepsilon_M$ modulo $M$ and a cusp form $g$ of weight $k$ on $\Gamma_1(M)$ with [`CuspForm.IsPrimitiveForm εM g`](def/CuspForm_PrimitiveFormGamma1.html#L38) — that is: `qCoeff g 1 = 1`, the analogous $T_p$-recursion with eigenvalue `qCoeff g p` holds for all primes $p\nmid M$, `qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n` for all primes $\ell\mid M$ and all $n$, $g$ has nebentypus $\varepsilon_M$, and for no proper divisor $M'$ of $M$ does the eigenpacket $(\,n\mapsto$ `qCoeff g n`$,\ n\mapsto\varepsilon_M(n)\,)$ occur at level $M'$ in the sense of `EigenpacketOccursAt` — such that for every prime $p\nmid N$ one has `qCoeff g p` $=\lambda(p)$ and $\varepsilon_M(p)=\varepsilon(p)$.
--
--   This is the Atkin–Lehner–Li theorem on the primitive form (newform) attached to a system of $T_p$-eigenvalues away from the level, in the form needed when the given eigenvector is not assumed normalised: it produces a newform of some level $M\mid N$ matching $\lambda(p)$ and $\varepsilon(p)$ at all primes $p\nmid N$. It is deduced from the decomposition of an arbitrary cusp form with nebentypus into oldform translates of primitive forms, and is used downstream in the level- and character-lowering steps that compare residual representations of modular forms of different levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus ε f) (lam : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam p * ModularFormClass.qCoeff f n) :
    ∃ (M : ℕ) (_ : NeZero M) (εM : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k),
      M ∣ N ∧ CuspForm.IsPrimitiveForm εM g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ModularFormClass.qCoeff g p = lam p ∧ εM (p : ZMod M) = ε (p : ZMod N) := by sorry
