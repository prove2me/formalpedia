-- Prove2me | Theorems.Thm_CuspForm_exists_diffQExp_eq_sum_smul_intSeriesC_of_mem_ssPolarDifferentials
-- name    : CuspForm.exists_diffQExp_eq_sum_smul_intSeriesC_of_mem_ssPolarDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/91e04e1f-d591-51bc-8ab7-63c3b318a821
-- title:
--   Supersingular polar differentials as reductions of two-cusp integral weight-two forms
-- statement:
--   Let $p$ be a prime and $M \ge 1$ an integer with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under $\mathbb{Z}\mathrm{Mod.unitsMap}$ for $M/p \mid M$ is trivial, and let $K$ be an algebraically closed field that is an algebra over $\mathbb{Z}/p$ (so of characteristic $p$). Write $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ for the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the map $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending a matrix to its lower right entry, and $\Gamma_{H'}(M/p)$ for the corresponding group attached to the image $H'$ of $H$ in $(\mathbb{Z}/(M/p))^\times$. Let $F =$ [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) $K\,\Gamma_{H'}(M/p)$, the subfield of $K((q))$ generated over $K$ by the quotients $\overline{p_f}/\overline{p_g}$ of mod-$p$ reductions of integral $q$-expansions of modular forms of equal weight on $\Gamma_{H'}(M/p)$, and let $\omega \in \Omega^1_{F/K}$ be a Kähler differential lying in [`ModularCurve.ssPolarDifferentials`](def/ModularCurve_XHDifferentialsModL.html#L35), i.e. $\omega$ is regular at every place of $F/K$ that is not supersingular (in the sense of `IsSSPlaceQExp`) and satisfies `Place.HasSimplePoleAt` at every supersingular place. Then there exist $n \in \mathbb{N}$, scalars $c_1,\dots,c_n \in K$, weight-two cusp forms $f_1,\dots,f_n$ on $\Gamma_H(M)$ and power series $p_1,\dots,p_n \in \mathbb{Z}[[q]]$ such that: each $f_i$ lies in [`CuspForm.twoCuspIntegralSet`](def/CuspForm_TwoCuspLattice.html#L54) for the prime subring $\bot \subseteq \mathbb{C}$, meaning that for every element $t$ of the Hecke subring `heckeRingH` of weight-two endomorphisms, every Atkin–Lehner datum $W$ for $M$ at $p$ (a factorisation $M = pR$ together with integers $a,b$ with $pa - Rb = 1$) and every index, the corresponding $q$-expansion coefficients of $t f_i$ and of the weight-two Atkin–Lehner slash $W \cdot (t f_i)$ are rational integers; each $p_i$ maps to the $q$-expansion of $f_i$ under $\mathbb{Z} \to \mathbb{C}$; and $$\mathrm{diffQExp}(\omega) = \sum_{i} c_i \cdot \overline{p_i} \quad \text{in } K((q)),$$ where $\mathrm{diffQExp}$ is the lift to $\Omega^1_{F/K}$ of the derivation $q\,d/dq$ on Laurent series restricted to $F$, and $\overline{p_i}$ is $p_i$ with coefficients reduced into $K$.
--
--   This is the surjectivity half of the identification, read purely on $q$-expansions, of the mod-$p$ reduction of the weight-two cusp forms on $\Gamma_H(M)$ that are two-cusp integral at $p$ with the space of differentials on $X_{H'}(M/p)$ over $K$ that are regular away from the supersingular points and have at most simple poles there. It feeds into [`CuspForm.exists_isInfReductionMap_range_eq_ssPolarDifferentials`](thm.html#CuspForm.exists_isInfReductionMap_range_eq_ssPolarDifferentials), where the two halves are combined into a statement about the range of the reduction map along the component through $\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_diffQExp_eq_sum_smul_intSeriesC_of_mem_ssPolarDifferentials.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CuspForm.exists_diffQExp_eq_sum_smul_intSeriesC_of_mem_ssPolarDifferentials
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (ω : Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hω : ω ∈ ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :
    ∃ (n : ℕ) (c : Fin n → K) (f : Fin n → CuspForm (CohCarrier.GammaH M H) 2)
      (pf : Fin n → PowerSeries ℤ),
      (∀ i, f i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) ∧
      (∀ i, ModularCurve.IsIntegralQExp (f i) (pf i)) ∧
      ModularCurve.diffQExp
          (ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω =
        ∑ i, c i • ModularCurve.intSeriesC K (pf i) := by sorry
