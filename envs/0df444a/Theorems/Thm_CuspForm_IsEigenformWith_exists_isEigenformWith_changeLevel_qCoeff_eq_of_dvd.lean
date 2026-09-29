-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd
-- name    : CuspForm.IsEigenformWith.exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/5412f18d-4e8b-5f15-b528-4e8f201c4a03
-- title:
--   Level raising of eigenforms with nebentypus along M ∣ N
-- statement:
--   Let $M$ be a natural number, $k$ an integer, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and $g$ a cusp form of weight $k$ for $\Gamma_1(M)$ which is an eigenform with character $\varepsilon$ in the coefficient sense: writing $a_n(g)$ for the $n$-th coefficient of the $q$-expansion of $g$ (the expansion `qExpansion 1`), one has $a_1(g)=1$; for every prime $p\nmid M$ and every $n$, $a_{pn}(g)+\varepsilon(p)\,p^{k-1}\,a_{n/p}(g)=a_p(g)a_n(g)$, the third term being present only when $p \mid n$; for every prime $\ell \mid M$ and every $n$, $a_{\ell n}(g)=a_\ell(g)a_n(g)$; and $g$ has nebentypus $\varepsilon$, i.e. $g(\gamma\tau)=\varepsilon(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^k g(\tau)$ for all $\gamma\in\Gamma_0(M)$ and all $\tau$ in the upper half-plane. Let $N$ be a nonzero natural number with $M \mid N$. Then there exists a cusp form $h$ of weight $k$ for $\Gamma_1(N)$ which is an eigenform in the same coefficient sense at level $N$, with character the Dirichlet character modulo $N$ obtained from $\varepsilon$ by `DirichletCharacter.changeLevel`, and such that $a_\ell(h)=a_\ell(g)$ for every prime $\ell$ satisfying $\ell\mid N\Rightarrow\ell\mid M$, that is, for every prime other than those dividing $N$ but not $M$.
--
--   This is the stabilisation (level-raising) step: an eigenform of level $M$ with nebentypus $\varepsilon$ produces an eigenform of any level $N$ divisible by $M$, with the induced character and with unchanged Hecke eigenvalues at all primes except those dividing $N$ but not $M$. It is used in the passage from a primitive form to eigenforms of the levels required by the Galois-representation arguments, in particular by the statements attaching $\ell$-adic representations with prescribed Frobenius characteristic polynomials and prescribed inertia behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.IsEigenformWith.exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd
    {M : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (hg : CuspForm.IsEigenformWith ε g) {N : ℕ} [NeZero N] (hMN : M ∣ N) :
    ∃ h : CuspForm (Gamma1 N) k,
      CuspForm.IsEigenformWith (DirichletCharacter.changeLevel hMN ε) h ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ ∣ N → ℓ ∣ M) →
        ModularFormClass.qCoeff h ℓ = ModularFormClass.qCoeff g ℓ := by sorry
