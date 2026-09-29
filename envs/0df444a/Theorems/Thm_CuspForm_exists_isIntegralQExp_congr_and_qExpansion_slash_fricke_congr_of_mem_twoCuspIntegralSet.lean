-- Prove2me | Theorems.Thm_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
-- name    : CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/1c459afd-549d-5b7a-af67-35ba283427fb
-- title:
--   Eisenstein trace congruence with Fricke transform at level M/p
-- statement:
--   Let $p$ be a prime and $M$ a positive integer with $p \mid M$ and $p^{2} \nmid M$, and let $H \le (\mathbb{Z}/M)^{\times}$ contain every unit whose image under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is $1$ (with $M/p$ nonzero). Let $\mathfrak{m}$ be a prime ideal of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$. Let `Wd` be an Atkin–Lehner datum for $(M, M/p)$, i.e. a factorisation $M = (M/p)R$ together with integers $a,b$ satisfying $(M/p)a - Rb = 1$; let $e \in (\mathbb{Z}/M)^{\times}$ have image in $\mathbb{Z}/(M/p)$ inverse to $p$, and let $W_Q \in \mathrm{GL}_2(\mathbb{R})$ have matrix $\begin{pmatrix}0&-1\\ M/p&0\end{pmatrix}$. Let $f$ be a weight-$2$ cusp form on $\Gamma_H(M)$ (the image in $\mathrm{SL}_2(\mathbb{Z})$ of those elements of $\Gamma_0(M)$ whose diagonal unit modulo $M$ lies in $H$) lying in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54): for every $t$ in the Hecke subring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ for $(M,p)$ and every $n$, the $n$-th $q$-coefficients at $\infty$ of $t f$ and of $(t f)\mid_2 W$ are rational integers. Let `pf` $\in \mathbb{Z}[[q]]$ have image in $\mathbb{C}[[q]]$ the $q$-expansion of $f$, let $D$ be a natural number prime to $p$, and let `pfW` be a power series over the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $D \cdot (\langle e\rangle f) \mid_2 W_d$, where $\langle e \rangle$ is [`CuspForm.diamondLinH 2 e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132). Then there exist $w \in \mathbb{N}$, a modular form $G$ of weight $2 + w$ on $\Gamma_{H'}(M/p)$ with $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, a power series $P \in \mathbb{Z}[[q]]$, natural numbers $D_1, D_2$, and a power series `PGW` over the integral closure, such that $w > 0$, $p - 1 \mid w$, $4 \mid w$, $p \nmid D_1$, $p \nmid D_2$, the image of $P$ in $\mathbb{C}[[q]]$ is the $q$-expansion of $G$, $p \mid P_n - D_1 \, (\mathrm{pf})_n$ in $\mathbb{Z}$ for all $n$, the image of `PGW` in $\mathbb{C}[[q]]$ is the $q$-expansion of $D_2 \cdot (G \mid_{2+w} W_Q)$, and $D \cdot (\mathrm{PGW})_n - D_2 D_1 (M/p)^{w} \, (\mathrm{pfW})_n \in \mathfrak{m}$ for all $n$.
--
--   This is the Eisenstein-trace congruence in the style of Serre: a two-cusp-integral weight-two form of level $M$ divisible exactly once by $p$ is matched, modulo $p$ and modulo $\mathfrak{m}$ respectively, by a single modular form of level $M/p$ and weight $2 + w$ with $w$ divisible by $p-1$ and by $4$, simultaneously at the cusp $\infty$ and after the Fricke transform $W_Q$ of level $M/p$. It supplies the analytic input for the compatibility of the reduction map on differentials of the component through $\infty$ with the Fricke involution, used by [`ModularCurve.IsInfReductionMap.smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke`](thm.html#ModularCurve.IsInfReductionMap.smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime)
    (hp𝔪 : ((p : ℕ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp ⇑f pf)
    (D : ℕ) (hD : ¬ p ∣ D)
    (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    ∃ (w : ℕ) (G : ModularForm (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) ((2 : ℤ) + w))
      (P : PowerSeries ℤ) (D₁ D₂ : ℕ) (PGW : PowerSeries ↥(integralClosure ℤ ℂ)),
      0 < w ∧ (p - 1 ∣ w) ∧ (4 ∣ w) ∧ ¬ p ∣ D₁ ∧ ¬ p ∣ D₂ ∧
      ModularCurve.IsIntegralQExp ⇑G P ∧
      (∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n P - (D₁ : ℤ) * PowerSeries.coeff n pf) ∧
      PGW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
        UpperHalfPlane.qExpansion 1 ((D₂ : ℂ) • ((⇑G : UpperHalfPlane → ℂ) ∣[(2 : ℤ) + w] WQ)) ∧
      (∀ n : ℕ, ((D : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n PGW -
          ((D₂ * D₁ * (M / p) ^ w : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n pfW ∈ 𝔪) := by sorry
