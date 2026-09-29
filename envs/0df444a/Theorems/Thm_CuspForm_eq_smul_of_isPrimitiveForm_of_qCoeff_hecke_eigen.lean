-- Prove2me | Theorems.Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
-- name    : CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/97abf573-2b45-5d03-8a1d-53a07d7c6d4a
-- title:
--   Multiplicity one at the level of a primitive form
-- statement:
--   Let $M \ge 1$ and $k \in \mathbb{Z}$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and write $\mathrm{qCoeff}\,h(n)$ for the $n$-th coefficient of the $q$-expansion of width $1$ of a function $h$ on the upper half plane. Let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$ which is primitive with character $\varepsilon$ in the sense of the project: $\mathrm{qCoeff}\,g(1) = 1$; for every prime $p \nmid M$ and every $n$, $\mathrm{qCoeff}\,g(pn) + \varepsilon(p)p^{k-1}\,[p \mid n]\,\mathrm{qCoeff}\,g(n/p) = \mathrm{qCoeff}\,g(p)\,\mathrm{qCoeff}\,g(n)$; for every prime $\ell \mid M$ and every $n$, $\mathrm{qCoeff}\,g(\ell n) = \mathrm{qCoeff}\,g(\ell)\,\mathrm{qCoeff}\,g(n)$; $g$ has nebentypus $\varepsilon$, i.e. $g(\gamma \tau) = \varepsilon(\gamma_{11})(\gamma_{10}\tau + \gamma_{11})^k g(\tau)$ for all $\gamma \in \Gamma_0(M)$ and all $\tau$; and, for every proper divisor $M'$ of $M$, the eigenpacket $\bigl(n \mapsto \mathrm{qCoeff}\,g(n),\ n \mapsto \varepsilon(n)\bigr)$ does not occur at level $M'$, meaning that there is no nonzero cusp form $h$ of weight $k$ for $\Gamma_1(M')$ with nebentypus some character $\varepsilon'$ modulo $M'$ and no finite set $S'$ of naturals such that for all primes $p \notin S'$ one has $\varepsilon'(p) = \varepsilon(p)$ together with $\mathrm{qCoeff}\,h(pn) + \varepsilon'(p)p^{k-1}\,[p \mid n]\,\mathrm{qCoeff}\,h(n/p) = \mathrm{qCoeff}\,g(p)\,\mathrm{qCoeff}\,h(n)$ for all $n$. Let $f$ be a cusp form of weight $k$ for $\Gamma_1(M)$ with nebentypus $\varepsilon$ in the same sense, and let $S$ be a finite set of naturals such that for every prime $p \notin S$ with $p \nmid M$ and every $n$, $\mathrm{qCoeff}\,f(pn) + \varepsilon(p)p^{k-1}\,[p \mid n]\,\mathrm{qCoeff}\,f(n/p) = \mathrm{qCoeff}\,g(p)\,\mathrm{qCoeff}\,f(n)$, that is, $T_p f = \mathrm{qCoeff}\,g(p)\, f$ for all but finitely many good primes. Then $f = \mathrm{qCoeff}\,f(1) \cdot g$.
--
--   This is the multiplicity-one statement of Atkin–Lehner and Li in the form used for newforms: inside the space of weight-$k$ cusp forms on $\Gamma_1(M)$ with nebentypus $\varepsilon$, a form sharing almost all the Hecke eigenvalues of a primitive form $g$ of the same level and character is a scalar multiple of $g$, the scalar being its first $q$-coefficient. It is used to identify newforms up to scalars from their eigenvalue packets, and underlies the normalisation and uniqueness steps in the passage from eigenvalue data to an actual modular form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (f : CuspForm (Gamma1 M) k)
    (hf : CuspForm.HasNebentypus ε f) (S : Finset ℕ)
    (hfS : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff g p * ModularFormClass.qCoeff f n) :
    f = ModularFormClass.qCoeff f 1 • g := by sorry
