-- Prove2me | Theorems.Thm_CuspForm_exists_infReductionMap_and_wReductionMap_range_le_ssPolarDifferentials
-- name    : CuspForm.exists_infReductionMap_and_wReductionMap_range_le_ssPolarDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/6990c792-f612-5333-bfff-7b235e7b46ca
-- title:
--   Two q-expansion-pinned reduction maps into ss-polar differentials
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under `ZMod.unitsMap` in $(\mathbb{Z}/(M/p))^\times$ is $1$, let $K$ be an algebraically closed field of characteristic $p$ that is an algebra over $\mathbb{Z}/p$, let $W$ be an Atkin–Lehner datum for $(M,p)$ (a factorisation $M = p\cdot R$ together with integers $a,b$ satisfying $pa - Rb = 1$), and let $e \in (\mathbb{Z}/M)^\times$ have image $\bar e$ in $\mathbb{Z}/(M/p)$ with $\bar e\cdot \bar p = 1$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))`](def/ModularCurve_X1.html#L101), the subfield of $K((q))$ generated over $K$ by the integral form ratios for $\Gamma_{H'}(M/p)$, $H'$ being the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Then there exist $K$-linear maps $\rho^\infty, \rho^0 : K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) $\to \Omega_{F/K}$ such that: $\rho^\infty$ satisfies [`ModularCurve.IsInfReductionMap`](def/ModularCurve_XHDifferentialsModL.html#L443), i.e. for every weight-two cusp form $f$ on $\Gamma_H(M)$ in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54) (all $q$-coefficients of $t f$ and of $t f \mid_2 W'$ lie in the bottom subring of $\mathbb{C}$, for all $t$ in the Hecke ring and all Atkin–Lehner data $W'$ at $(M,p)$) and every $p_f \in \mathbb{Z}[[q]]$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $f$, the Laurent-series image `diffQExp` of $\rho^\infty(1 \otimes \overline{f})$ equals `intSeriesC K` $p_f$, where $\overline{f}$ is the reduction of $f$ in `IntTwoCuspForms`; correspondingly, for every such $f$ and every $p_{f,W} \in \mathbb{Z}[[q]]$ that is an integral $q$-expansion of $(\langle e \rangle f)\mid_2 W$, `diffQExp` of $\rho^0(1 \otimes \overline{f})$ equals `intSeriesC K` $p_{f,W}$; and the ranges of both $\rho^\infty$ and $\rho^0$ lie in [`ModularCurve.ssPolarDifferentials`](def/ModularCurve_XHDifferentialsModL.html#L35), the $K$-submodule of differentials regular away from the supersingular places of $F$ and with at most a simple pole at each of them.
--
--   Classically the two maps are the restrictions, to the two components of the reduction of $X_H(M)$ at $p$ (the second in the $w_p$-transported coordinate), of the reduction of the regular differential attached to a weight-two form, with the two pinnings expressing the $q$-expansion principle at the cusps $\infty$ and $w_p\infty$. It supplies the reduction maps used by [`ModularCurve.exists_linearEquiv_intTwoCuspForms_twoCompRegularDifferentials`](thm.html#ModularCurve.exists_linearEquiv_intTwoCuspForms_twoCompRegularDifferentials) and [`ModularCurve.finrank_tensorProduct_intTwoCuspForms_eq_finrank_twoCompRegularDifferentials`](thm.html#ModularCurve.finrank_tensorProduct_intTwoCuspForms_eq_finrank_twoCompRegularDifferentials); the containments of the ranges are inclusions only, equality being a separate matter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_infReductionMap_and_wReductionMap_range_le_ssPolarDifferentials.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.exists_infReductionMap_and_wReductionMap_range_le_ssPolarDifferentials
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1) :
    ∃ (ρinf ρzero : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]),

      ModularCurve.IsInfReductionMap K p M H hpM ρinf ∧

      (∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (pfW : PowerSeries ℤ), ModularCurve.IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
            ModularCurve.diffQExp
                (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
                (ρzero ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                  ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
              ModularCurve.intSeriesC K pfW) ∧

      LinearMap.range ρinf ≤ ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p ∧
      LinearMap.range ρzero ≤ ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by sorry
