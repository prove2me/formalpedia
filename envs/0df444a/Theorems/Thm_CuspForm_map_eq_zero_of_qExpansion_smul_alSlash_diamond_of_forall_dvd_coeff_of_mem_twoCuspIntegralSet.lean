-- Prove2me | Theorems.Thm_CuspForm_map_eq_zero_of_qExpansion_smul_alSlash_diamond_of_forall_dvd_coeff_of_mem_twoCuspIntegralSet
-- name    : CuspForm.map_eq_zero_of_qExpansion_smul_alSlash_diamond_of_forall_dvd_coeff_of_mem_twoCuspIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/7a391aa7-c858-5de5-a96c-0ba5b05dca6a
-- title:
--   Mod p vanishing of an Atkin–Lehner–diamond translate
-- statement:
--   Let $p$ be prime and $M$ a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ contain every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Fix an Atkin–Lehner datum $W_d$ for $(M, M/p)$ — that is, data $R, a, b$ with $M = (M/p)R$ and $(M/p)a - Rb = 1$ — a unit $e \in (\mathbb{Z}/M)^\times$, a field $K$ and a ring homomorphism $\varphi$ from the ring of algebraic integers $\overline{\mathbb{Z}} = \mathrm{integralClosure}\ \mathbb{Z}\ \mathbb{C}$ to $K$ with $\varphi(p) = 0$. Let $x$ be a weight $2$ cusp form for $\Gamma_H(M)$, the preimage in $\Gamma_0(M)$ of $H$ under the lower-right-entry character, and assume $x$ lies in the project's two-cusp integrality set for the subring $\bot \subseteq \mathbb{C}$ (the image of $\mathbb{Z}$) at $p$: for every element $t$ of the Hecke subring `heckeRingH`, every Atkin–Lehner datum $W$ for $(M,p)$ and every $n$, the $n$-th coefficients of the $q$-expansions of $t x$ and of $W$-slashed $t x$ are rational integers. Suppose $pf \in \mathbb{Z}[[q]]$ maps to the $q$-expansion of $x$ at $\infty$ (period $1$) and that $p$ divides every coefficient of $pf$. Then for every $D \in \mathbb{N}$ and every $pfW \in \overline{\mathbb{Z}}[[q]]$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $D \cdot \bigl(\langle e \rangle x\bigr)\mid_2 W_d$, one has $\varphi(pfW) = 0$ in $K[[q]]$. Here $\langle e \rangle$ is [`CuspForm.diamondLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), the slash by a lift of $e$ to $\mathrm{SL}_2(\mathbb{Z})$ when the project's cusp-stability condition `StableD` holds in weight $2$, and the zero map otherwise.
--
--   This is a $q$-expansion integrality statement: congruence to zero modulo $p$ of the expansion of $x$ at the cusp $\infty$ propagates, after applying a diamond operator and the Atkin–Lehner involution at $M/p$, to vanishing modulo any maximal ideal of $\overline{\mathbb{Z}}$ through which $\varphi$ factors. It is used in the comparison of polarised differentials with Atkin–Lehner pinning on the modular curve, and in the corresponding statement for forms presented directly as a multiple of an Atkin–Lehner–diamond translate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_map_eq_zero_of_qExpansion_smul_alSlash_diamond_of_forall_dvd_coeff_of_mem_twoCuspIntegralSet.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.map_eq_zero_of_qExpansion_smul_alSlash_diamond_of_forall_dvd_coeff_of_mem_twoCuspIntegralSet
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (K : Type*) [Field K] (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)
    (x : CuspForm (CohCarrier.GammaH M H) 2) (hx : x ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp (⇑x) pf) (hp0 : ∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n pf)
    (D : ℕ) (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e x))) :
    pfW.map φ = 0 := by sorry
