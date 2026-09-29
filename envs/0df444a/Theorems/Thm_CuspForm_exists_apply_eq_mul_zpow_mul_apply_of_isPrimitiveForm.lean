-- Prove2me | Theorems.Thm_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
-- name    : CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/316bb789-342d-533f-a0ba-3e25ac4e736a
-- title:
--   Pseudo-eigenvalue of the Fricke involution on a primitive form
-- statement:
--   Let $M$ be a nonzero natural number, $k$ an integer, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $g$ be a cusp form of weight $k$ on $\Gamma_1(M)$. Write $\mathrm{qCoeff}\,f\,n$ for the $n$-th coefficient of the $q$-expansion of $f$ with width $1$. Assume [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38) $\varepsilon\,g$, that is: $\mathrm{qCoeff}\,g\,1 = 1$; for every prime $p \nmid M$ and every $n$, $\mathrm{qCoeff}\,g\,(pn) + \varepsilon(p)p^{k-1}\,[\,p \mid n\,]\,\mathrm{qCoeff}\,g\,(n/p) = \mathrm{qCoeff}\,g\,p \cdot \mathrm{qCoeff}\,g\,n$; for every prime $\ell \mid M$ and every $n$, $\mathrm{qCoeff}\,g\,(\ell n) = \mathrm{qCoeff}\,g\,\ell \cdot \mathrm{qCoeff}\,g\,n$; the predicate `HasNebentypus` $\varepsilon\,g$ holds; and for no proper divisor $M'$ of $M$ does the eigenpacket $(\mathrm{qCoeff}\,g\,p,\ \varepsilon(p))$ occur at level $M'$, i.e. there is no nonzero cusp form $h$ of weight $k$ on $\Gamma_1(M')$ with some nebentypus $\varepsilon'$ modulo $M'$ and some finite set $S$ of primes such that for all primes $p \notin S$ one has $\varepsilon'(p) = \varepsilon(p)$ and $h$ satisfies the corresponding $T_p$-relation with eigenvalue $\mathrm{qCoeff}\,g\,p$. Let $g'$ be a cusp form of weight $k$ on $\Gamma_1(M)$ whose $q$-coefficients are the complex conjugates of those of $g$. Then there is $c \neq 0$ such that for all $\tau, \tau'$ in the upper half-plane with $\tau' \cdot (M\tau) = -1$ one has $g(\tau') = c\,\tau^{k}\,g'(\tau)$.
--
--   This is the statement that the Fricke involution $W_M = \begin{pmatrix}0&-1\\M&0\end{pmatrix}$ carries a primitive form of level $M$, weight $k$ and nebentypus $\varepsilon$ to a nonzero multiple of its conjugate form, the constant $c$ being the pseudo-eigenvalue of $W_M$ in the sense of Atkin–Li. It is used in the project's analysis of slashed sums for primitive forms and in the construction of weight-one newforms from an eigenpacket of $q$-coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = c * (τ : ℂ) ^ k * g' τ := by sorry
