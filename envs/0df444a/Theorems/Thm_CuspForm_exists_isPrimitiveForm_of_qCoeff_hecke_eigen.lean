-- Prove2me | Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen
-- name    : CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/f0fb6f54-9883-5c61-b0c4-32c3ac94b655
-- title:
--   Existence of an attached primitive form (Atkin–Lehner–Li)
-- statement:
--   Let $N$ be a positive natural number, $k$ an integer, and $f$ a cusp form of weight $k$ on $\Gamma_1(N)$, whose coefficients are taken via [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19), the coefficients of the $q$-expansion of width $1$. Assume the first coefficient of $f$ is $1$, and let $\chi : \mathbb{N} \to \mathbb{C}$ be a function such that for every prime $p \nmid N$ and every $n$ one has $a_{pn} + \chi(p)\,[p \mid n]\,a_{n/p} = a_p a_n$, where $a_m$ denotes the $m$-th coefficient of $f$ (the bracket being the $q$-coefficient $a_{n/p}$ when $p \mid n$ and $0$ otherwise). Then there exist a positive $M$ dividing $N$, a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$, and a cusp form $g$ of weight $k$ on $\Gamma_1(M)$ such that $g$ is primitive with character $\varepsilon$ in the sense of [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38), and such that for every prime $p \nmid N$ the $p$-th coefficient of $g$ equals $a_p$ and $\varepsilon(p)\,p^{k-1} = \chi(p)$. Primitivity means: the first coefficient of $g$ is $1$; for every prime $p \nmid M$ and all $n$, $b_{pn} + \varepsilon(p)p^{k-1}[p\mid n]\,b_{n/p} = b_p b_n$; for every prime $\ell \mid M$ and all $n$, $b_{\ell n} = b_\ell b_n$; $g$ satisfies `HasNebentypus` with respect to $\varepsilon$; and for no divisor $M' \neq M$ of $M$ does the eigenpacket $(n \mapsto b_n, n \mapsto \varepsilon(n))$ occur at level $M'$, i.e. there is no Dirichlet character $\varepsilon'$ modulo $M'$ and nonzero cusp form $h$ of weight $k$ on $\Gamma_1(M')$ with nebentypus $\varepsilon'$ for which, outside some finite set of primes, $\varepsilon'(p) = \varepsilon(p)$ and $h$ satisfies the corresponding Hecke relation at $p$ with eigenvalue $b_p$.
--
--   This is the Atkin–Lehner–Li theory of newforms in coefficient form: a normalised cusp form satisfying the Hecke eigenrelations at the primes away from the level has an attached primitive form of some level dividing $N$ with the same eigenvalues outside $N$, the multiplier $\chi(p)$ being identified with $\varepsilon(p)p^{k-1}$. It is obtained by first producing a nebentypus for $f$ and then decomposing $f$ into contributions of primitive forms of levels dividing $N$, and it is used in the passage from Hecke eigenforms to newforms, in particular in weight one and in the Deligne–Serre coefficient estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (χ : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            χ p * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ (M : ℕ) (_ : NeZero M) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k),
      M ∣ N ∧ CuspForm.IsPrimitiveForm ε g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ModularFormClass.qCoeff g p = ModularFormClass.qCoeff f p ∧
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) = χ p := by sorry
