-- Prove2me | Theorems.Thm_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
-- name    : CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/d47fc2a8-082d-573f-9e24-4f2a3c6321ef
-- title:
--   Atkin–Lehner operator at p commutes with T_ℓ
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime dividing $M$, and $H$ a subgroup of $(\mathbb{Z}/M)^{\times}$ with the property that every unit $u$ whose image under the reduction map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is trivial already lies in $H$. Let $W$ be an Atkin–Lehner datum for $(M,p)$, that is, a natural number $R$ with $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$; write $W$ also for the associated invertible real matrix `ModularForm.alGL`, and $f \mapsto f \mid_k W$ for the resulting weight-$k$ slash operator [`ModularForm.alSlash`](def/ModularForm_AtkinLehnerDatum.html#L141). Let $k$ be an integer and $\ell$ a prime not dividing $M$. Finally let $f$ and $X$ be cusp forms of weight $k$ on $\Gamma_H(M)$ — the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the matrices in $\Gamma_0(M)$ whose lower-right entry reduces into $H$ — such that the function underlying $X$ is $f \mid_k W$. The conclusion is the equality of functions $\mathbb{H} \to \mathbb{C}$
--   $$(T_\ell f)\mid_k W = T_\ell X,$$
--   where $T_\ell$ denotes [`CuspForm.heckeTLinH k hℓ hℓM`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224), the $\mathbb{C}$-linear endomorphism of weight-$k$ cusp forms on $\Gamma_H(M)$ sending $g$ to [`ModularForm.heckeU k ℓ g`](def/ModularForm_HeckeOperator.html#L93) plus the slash of $g$ by the product of a lift in $\Gamma_0(M)$ with lower-right entry congruent to $\ell$ mod $M$ and the matrix [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21) (the degenerate branch of this definition is excluded, since [`CuspForm.stableT`](thm.html#CuspForm.stableT) provides the stability hypothesis `StableT M H k ℓ` for $\ell$ prime and $\ell \nmid M$). Thus no diamond twist appears: the hypothesis on $H$ forces the relevant diamond operator to be the identity.
--
--   This is the Atkin–Lehner commutation relation $(T_\ell f)\mid W = T_\ell\langle v\rangle (f\mid W)$, with $v \equiv \ell^{-1} \bmod p$ and $v \equiv 1 \bmod M/p$, in the case where the nebentypus group $H$ contains all units congruent to $1$ modulo $M/p$, so that the diamond operator $\langle v\rangle$ disappears. It feeds the arguments that integrality of $q$-expansion coefficients at two cusps is preserved by the Hecke operators $T_\ell$ and by the generated Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f X : CuspForm (CohCarrier.GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.heckeTLinH k hℓ hℓM f) = ⇑(CuspForm.heckeTLinH k hℓ hℓM X) := by sorry
