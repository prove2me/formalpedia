-- Prove2me | Theorems.Thm_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus
-- name    : CuspForm.exists_gammaH_coe_eq_of_hasNebentypus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/876311f6-325d-5a0d-84dd-4ff5f68715f9
-- title:
--   Cusp forms with nebentypus trivial on H descend to Γ_H(M)
-- statement:
--   Let $M$ be a positive natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, $k$ an integer, and $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$ such that $\varepsilon(d)=1$ for every unit $d\in H$ (applied to the image of $d$ in $\mathbb{Z}/M$). Let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$ satisfying [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) for $\varepsilon$, i.e. for every $\gamma\in SL(2,\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau$ in the upper half-plane, $g(\gamma\cdot\tau)=\varepsilon(\gamma_{11}\bmod M)\,\bigl((\gamma_{10}\tau+\gamma_{11})^{k}\,g(\tau)\bigr)$. Then there is a cusp form $f$ of weight $k$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) — the image in $SL(2,\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$ sending $\gamma$ to the unit with value $\gamma_{11}\bmod M$ and inverse $\gamma_{00}\bmod M$, i.e. the group of $\gamma\in\Gamma_0(M)$ whose lower-right entry reduces into $H$ — whose underlying function $\mathfrak{H}\to\mathbb{C}$ equals that of $g$.
--
--   This is one half of the identification of $S_k(\Gamma_H(M))$ with the sum of the nebentypus eigenspaces $S_k(M,\varepsilon)$ for characters $\varepsilon$ trivial on $H$, realised here at the level of underlying functions: a $\Gamma_1(M)$-cusp form with nebentypus killed by $H$ is already invariant for $\Gamma_H(M)$. It is used in the construction of bases of primitive forms at level $\Gamma_H$ and in the analysis of Hecke and diamond operators and old classes there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gammaH_coe_eq_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (hε : ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.HasNebentypus ε g) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) k, (⇑f : UpperHalfPlane → ℂ) = ⇑g := by sorry
