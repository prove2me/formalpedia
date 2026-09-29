-- Prove2me | Theorems.Thm_CuspForm_add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC
-- name    : CuspForm.add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/9b91c1af-3104-56d2-86fb-9a9195e35009
-- title:
--   Regularity of Cω_f+ω_{⟨ d⟩ h} in characteristic p
-- statement:
--   Let $p$ be prime, let $M$ be a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ contain every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Let $K$ be an algebraically closed field of characteristic $p$, an algebra over $\mathbb{Z}/p$, and write $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M/p) (ModularCurve.infSubgroup p M H hpM))`](def/ModularCurve_X1.html#L101) for the subfield of $K((q))$ generated over $K$ by the integral form ratios attached to $\Gamma_{H'}(M/p)$, where $H'$ is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Let $W$ be an Atkin–Lehner datum for $(M,p)$, that is, a factorisation $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$. Let $e \in (\mathbb{Z}/M)^\times$ have image $\bar e$ with $\bar e\, \bar p = 1$ in $\mathbb{Z}/(M/p)$, and let $d \in (\mathbb{Z}/M)^\times$ have image $\bar p$ in $\mathbb{Z}/(M/p)$. Let $C$ be a $K$-linear endomorphism of $\Omega_{F/K}$ satisfying [`ModularCurve.IsFrobPushDiff`](def/ModularCurve_XHDifferentialsModL.html#L97), i.e. $\mathrm{diffQExp}(C\omega) = \mathrm{qDecimate}_p(\mathrm{diffQExp}\,\omega)$ for all $\omega$, where $\mathrm{diffQExp}$ is the $F$-linear map on Kähler differentials induced by the $q$-Euler derivation on $F$. Let $f$ be a weight-two cusp form for $\Gamma_H(M)$ lying in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54): for every element $t$ of the Hecke ring `heckeRingH M H 2`, every Atkin–Lehner datum and every $n$, the $n$-th $q$-coefficients of $t f$ and of the Atkin–Lehner slash of $t f$ lie in the subring $\bot \subseteq \mathbb{C}$. Let $h$ be a weight-two cusp form for $\Gamma_H(M)$ whose underlying function is $\mathrm{alSlash}_W(\langle e\rangle f)$, and let $p_f$, $p_{\langle d\rangle h}$ be power series over $\mathbb{Z}$ whose images in $\mathbb{C}[[q]]$ are the $q$-expansions of $f$ and of $\langle d\rangle h$ respectively. Finally let $\omega, \omega' \in \Omega_{F/K}$ satisfy $\mathrm{diffQExp}(\omega) = \mathrm{intSeriesC}_K(p_f)$ and $\mathrm{diffQExp}(\omega') = \mathrm{intSeriesC}_K(p_{\langle d\rangle h})$, the reductions mod $p$ of the two integral series viewed in $K((q))$. Then $C\omega + \omega'$ lies in [`AlgebraicCurve.regularDifferentials K F`](def/AlgebraicCurve_RegularDifferentials.html#L26), i.e. for every place $v$ of $F$ over $K$ (a valuation subring of $F$, proper, containing the image of $K$, and a principal ideal ring) there is an element $g$ of the valuation subring of $v$ with $C\omega + \omega' = g \cdot v.\mathrm{dCoord}$.
--
--   This is the differential-theoretic form, in characteristic $p$, of the Atkin–Lehner trace identity $U_p + W$ at a level exactly divisible by $p$: the combination $C\omega + \omega'$ of the Frobenius push of the differential attached to $f$ and the differential attached to $\langle d\rangle h$ has the $q$-expansion of a weight-two cusp form of the lower level $\Gamma_{H'}(M/p)$, hence is regular. It feeds the construction of differentials with prescribed polar behaviour used in the level-lowering step, being cited by [`CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet`](thm.html#CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet) and [`CuspForm.mem_twoCompRegularDifferentials_of_diffQExp_eq_intSeriesC_of_diffQExp_eq_intSeriesC_alSlash`](thm.html#CuspForm.mem_twoCompRegularDifferentials_of_diffQExp_eq_intSeriesC_of_diffQExp_eq_intSeriesC_alSlash).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (C : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hC : ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p C)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (h : CuspForm (CohCarrier.GammaH M H) 2) (hh : ⇑h = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f))
    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (pf pdh : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf)
    (hpdh : ModularCurve.IsIntegralQExp ⇑(CuspForm.diamondLinH 2 d h) pdh)
    (ω ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hω : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω = ModularCurve.intSeriesC K pf)
    (hω' : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω' = ModularCurve.intSeriesC K pdh) :
    C ω + ω' ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := by sorry
