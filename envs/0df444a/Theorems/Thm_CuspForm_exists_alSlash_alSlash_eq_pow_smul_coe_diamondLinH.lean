-- Prove2me | Theorems.Thm_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
-- name    : CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/7382efa2-559c-5ba7-a0ce-079020aeed0d
-- title:
--   Two Atkin–Lehner slashes compose to p^{k-2} times a diamond
-- statement:
--   Fix $M \ge 1$ and a prime $p$ dividing $M$, and let $H \le (\mathbb{Z}/M)^{\times}$ be a subgroup satisfying the hypothesis `hHp`: every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction map `ZMod.unitsMap` associated with the divisibility $(M/p) \mid M$ is trivial already lies in $H$ (so $H$ contains all units congruent to $1$ modulo $M/p$). Let $W$ and $W'$ be Atkin–Lehner data at $(M,p)$, each consisting of a natural number $R$ with $M = pR$ together with integers $a, b$ satisfying $pa - Rb = 1$, let $k \in \mathbb{Z}$, and let $f$ be a cusp form of weight $k$ for the group $\Gamma_H(M)$, i.e. the image in $\mathrm{SL}(2,\mathbb{Z})$ of those elements of $\Gamma_0(M)$ whose associated unit under `gamma0Units` lies in $H$. The assertion is that there exists $\delta \in (\mathbb{Z}/M)^{\times}$ with
--   $$\big(f \mid_k W'_{\mathbb{R}}\big)\big|_k W_{\mathbb{R}} \;=\; p^{\,k-2} \cdot \big(\langle \delta \rangle f\big),$$
--   an equality of functions on the upper half-plane; here $W_{\mathbb{R}}$ denotes the invertible real matrix `alGL` attached to the datum, $\mid_k$ the weight-$k$ slash action, $p^{k-2}$ the complex integer power, and $\langle \delta \rangle f =$ `diamondLinH k δ f` is the slash of $f$ by a lift `gammaLift M δ` of $\delta$ to $\mathrm{SL}(2,\mathbb{Z})$, which is the operative description because [`CuspForm.stableD`](thm.html#CuspForm.stableD) guarantees the predicate `StableD` used in the definition of `diamondLinH` holds.
--
--   This is the two-datum form of the Atkin–Lehner $W^2$-law at a prime $p$ exactly dividing the level's $p$-part data: the product of two Atkin–Lehner matrices at $(M,p)$ lies in $p \cdot \Gamma_0(M)$, whence the double slash is the scalar $p^{k-2}$ times a diamond operator. It is used in the analysis of $q$-expansion integrality at the two cusps and in the compatibility of the diamond operators with the Hecke operators $T_\ell$ and $U_p$ on $\Gamma_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W W' : ModularForm.AtkinLehnerDatum M p) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ δ : (ZMod M)ˣ, ModularForm.alSlash W k (ModularForm.alSlash W' k ⇑f) =
      ((p : ℂ) ^ (k - 2)) • (⇑(CuspForm.diamondLinH k δ f) : UpperHalfPlane → ℂ) := by sorry
