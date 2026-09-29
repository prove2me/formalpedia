-- Prove2me | Theorems.Thm_CuspForm_map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff
-- name    : CuspForm.map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/e07f8891-a657-58b1-89a7-66c59d3d8022
-- title:
--   Atkin–Lehner–diamond twist preserves vanishing modulo p
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Fix Atkin–Lehner data $W_p$ for $(M,p)$ and $W_d$ for $(M,M/p)$ — each consisting of a cofactor $R$ with $M = q R$ and integers $a,b$ with $qa - Rb = 1$ for the relevant $q$ — a unit $e \in (\mathbb{Z}/M)^\times$, a field $K$ and a ring homomorphism $\varphi$ from the ring $\overline{\mathbb{Z}}$ of algebraic integers (the integral closure of $\mathbb{Z}$ in $\mathbb{C}$) to $K$ with $\varphi(p) = 0$. Let $x$ be a weight-$2$ cusp form on the group $\Gamma_H(M)$, the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the lower-right-entry character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$, and assume $x$ lies in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54): for every element $t$ of the Hecke subring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ for $(M,p)$ and every $n$, the $n$-th coefficient of the width-$1$ $q$-expansion at $\infty$ of $t x$ and that of $(t x) \mid_2 W$ both lie in the bottom subring of $\mathbb{C}$, i.e. are rational integers. Here $\langle e \rangle$ denotes [`CuspForm.diamondLinH 2 e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), the endomorphism given by slashing in weight $2$ by a lift of $e$ to $\mathrm{SL}_2(\mathbb{Z})$ (it is this slash operator, the stability predicate `StableD M H 2` being satisfied, and the zero map otherwise). Assume a power series $pf_0 \in \mathbb{Z}[[q]]$ whose image in $\mathbb{C}[[q]]$ is the width-$1$ $q$-expansion at $\infty$ of $(\langle e \rangle x) \mid_2 W_p$, and that $p$ divides every coefficient of $pf_0$. Assume further a natural number $D$ and a cusp form $g$ on $\Gamma_H(M)$ of weight $2$ with $g = D \cdot \big((\langle e \rangle x) \mid_2 W_d\big)$ as functions on the upper half-plane, and a power series $pg_W$ with algebraic integer coefficients whose image in $\mathbb{C}[[q]]$ is the width-$1$ $q$-expansion at $\infty$ of $(\langle e \rangle g) \mid_2 W_p$. Then the image of $pg_W$ under $\varphi$ is the zero power series over $K$.
--
--   This is the stability, under the twist by $W_{M/p}$ followed by a diamond operator, of vanishing modulo $p$ along the component of the modular curve through the cusp $0$: congruence to zero for $(\langle e\rangle x)\mid_2 W_p$ propagates to $(\langle e\rangle g)\mid_2 W_p$ after applying $\varphi$. It is used in the construction of regular differentials pinned along a component by an Atkin–Lehner involution, in [`ModularCurve.coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong`](thm.html#ModularCurve.coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wp : ModularForm.AtkinLehnerDatum M p) (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (K : Type*) [Field K] (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)
    (x : CuspForm (CohCarrier.GammaH M H) 2) (hx : x ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf0 : PowerSeries ℤ) (hpf0 : ModularCurve.IsIntegralQExp (ModularForm.alSlash Wp 2 ⇑(CuspForm.diamondLinH 2 e x)) pf0)
    (hp0 : ∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n pf0)
    (D : ℕ) (g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : (⇑g : UpperHalfPlane → ℂ) = (D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e x))
    (pgW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpgW : pgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 (ModularForm.alSlash Wp 2 ⇑(CuspForm.diamondLinH 2 e g))) :
    pgW.map φ = 0 := by sorry
