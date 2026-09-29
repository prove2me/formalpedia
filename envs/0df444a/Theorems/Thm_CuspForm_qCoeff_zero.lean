-- Prove2me | Theorems.Thm_CuspForm_qCoeff_zero
-- name    : CuspForm.qCoeff_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/05ad4461-c72a-54b6-a4ee-0f0454bcf0b6
-- title:
--   Vanishing constant term of a cusp form on Γ₀(N)
-- statement:
--   Let $N$ be a natural number and $k$ an integer, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(N)$, i.e. an element of `CuspForm (CongruenceSubgroup.Gamma0 N) k`. Write $q$-expansions with respect to the period $1$: for a function $g \colon \mathbb{H} \to \mathbb{C}$, the project's coefficient function [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) is defined by $\mathrm{qCoeff}(g, n) =$ the $n$-th coefficient of the formal power series `qExpansion 1 g`, the $q$-expansion of $g$ of period $1$, so that $q = e^{2\pi i \tau}$. The assertion is that for the underlying function of $f$ on the upper half-plane, the coefficient of index $0$ vanishes: $\mathrm{qCoeff}(f, 0) = 0$. No hypotheses beyond the membership of $f$ in the space of cusp forms are imposed; in particular $N$ is arbitrary (including $N = 0$) and $k$ is an arbitrary integer.
--
--   This is the standard fact that a cusp form has no constant term in its $q$-expansion at the cusp $\infty$, recorded for the coefficient function [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) used throughout the treatment of normalised eigenforms; among its consumers are the statements relating Hecke eigenvalues of a normalised eigenform to its $q$-coefficients and their integrality, where the index $n = 0$ case becomes automatic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.qCoeff_zero {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ModularFormClass.qCoeff f 0 = 0 := by sorry
