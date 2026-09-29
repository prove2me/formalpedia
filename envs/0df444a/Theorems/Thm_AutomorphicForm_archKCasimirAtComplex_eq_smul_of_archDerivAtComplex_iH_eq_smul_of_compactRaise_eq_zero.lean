-- Prove2me | Theorems.Thm_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
-- name    : AutomorphicForm.archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/297e50b7-c227-5744-8314-5902d9c3d6d1
-- title:
--   Compact Casimir acts by -(n²+2n) on highest-weight vectors
-- statement:
--   Let $F$ be a number field, let $w$ be an infinite place of $F$ with $w$ complex (witnessed by `hw`), and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function on the adelic general linear group $\mathrm{GL}_2$ over the adele ring of $\mathcal{O}_F$ and $F$. Assume `IsArchSmoothAtComplex hw φ`: for every $g$ the map sending a $2\times 2$ complex matrix $e$ to $\varphi(g\cdot \iota_w(e))$, where $\iota_w$ places $e$ in the factor at $w$ when $\det e \neq 0$ (and $1$ otherwise), is $C^\infty$ on the set $\{e : \det e \neq 0\}$. Let $n$ be a natural number. Assume two conditions on the directional derivatives $D_d\varphi(g) = \frac{d}{dt}\varphi\bigl(g\cdot \iota_w(\exp\text{-flow}_d(t))\bigr)|_{t=0}$ attached to the six directions $H, E, F^-, iH, iE, iF^-$: the weight condition $D_{iH}\varphi = (in)\varphi$, and the highest-weight (annihilation) condition $D_{F^-}\varphi - D_E\varphi + i\,(D_{iE}\varphi + D_{iF^-}\varphi) = 0$. Then the compact Casimir expression $$D_{iH}D_{iH}\varphi + \bigl(D_E - D_{F^-}\bigr)\bigl(D_E\varphi - D_{F^-}\varphi\bigr) + \bigl(D_{iE} + D_{iF^-}\bigr)\bigl(D_{iE}\varphi + D_{iF^-}\varphi\bigr)$$ equals $-(n^2 + 2n)\,\varphi$.
--
--   This is the computation of the eigenvalue of the $\mathrm{SU}(2)$-Casimir operator, written as the sum of the squares of the three compact directions at a complex place, on a vector of circle weight $n$ annihilated by the corresponding raising operator; the eigenvalue $-(n^2+2n)$ is that of the $(n+1)$-dimensional $K$-type. It is used in the lower bound for the real part of the Casimir scalars of a cuspidal constituent at a complex place, [`AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex`](thm.html#AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (n : ℕ)
    (hwt : archDerivAtComplex hw .iH φ = (Complex.I * (n : ℂ)) • φ)
    (hJ : archDerivAtComplex hw .Fm φ - archDerivAtComplex hw .E φ
      + Complex.I • (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ) = 0) :
    archKCasimirAtComplex hw φ = (-(((n : ℂ) ^ 2 + 2 * (n : ℂ)))) • φ := by sorry
