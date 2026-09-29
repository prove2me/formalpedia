-- Prove2me | Theorems.Thm_CuspForm_exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp
-- name    : CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/51f21e7c-42eb-5ab5-9c6f-be6007d81827
-- title:
--   Mod p differential from an integral weight-two cusp form
-- statement:
--   Let $p$ be a prime, let $M \ge 1$ satisfy $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Let $K$ be an algebraically closed field equipped with a $\mathbb{Z}/p$-algebra structure, and let $f$ be a cusp form of weight $2$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained by pulling $H$ back along the character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower right entry. Suppose $pf \in \mathbb{Z}[[q]]$ satisfies [`ModularCurve.IsIntegralQExp f pf`](def/ModularCurve_X1.html#L37), i.e. the image of $pf$ in $\mathbb{C}[[q]]$ is the $q$-expansion of $f$ of width $1$. Write $\Gamma' =$ [`CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)`](def/CohCarrier_Level.html#L133), the analogous subgroup attached to $M/p$ and to the image $H'$ of $H$ in $(\mathbb{Z}/(M/p))^\times$, and let $F' =$ [`ModularCurve.qExpFunctionFieldC K Γ'`](def/ModularCurve_X1.html#L101) be the subfield of $K((q))$ generated over $K$ by the quotients $\mathrm{intSeriesC}_K(p_g)/\mathrm{intSeriesC}_K(p_h)$ of reductions of integral $q$-expansions of modular forms of equal weight for $\Gamma'$. The assertion is that there exists $\omega \in \Omega_{F'/K}$ such that, first, for every place $v$ of $F'$ over $K$ (a valuation subring containing $K$, distinct from $F'$ and a principal ideal ring) which does not lie in [`ModularCurve.ssPlacesQExp K Γ' p`](def/ModularCurve_XHDifferentialsModL.html#L27) — the set of places at which the element of $F'$ whose Laurent series is `jqModC K` takes a value lying in the supersingular $j$-set `ssJSet p K` — the differential $\omega$ is regular at $v$, meaning $\omega = g \cdot d(\pi_v)$ for some $g$ in the valuation subring of $v$ and $\pi_v$ a uniformiser; and second, the $q$-expansion [`ModularCurve.diffQExp`](def/ModularCurve_HeckeDifferential.html#L128) of $\omega$, obtained by lifting the derivation $q\,d/dq$ on $K((q))$ to Kähler differentials, equals [`ModularCurve.intSeriesC K pf`](def/ModularCurve_X1.html#L69), the Laurent series obtained from $pf$ by reducing its coefficients into $K$.
--
--   This is the smooth-locus half of the existence statement underlying mod $p$ level lowering at $p$: the mod $p$ reduction of a weight-two cusp form on $\Gamma_H(M)$, integral at $\infty$, is realised as the $q$-expansion of a differential on the curve of level $\Gamma_{H'}(M/p)$ over $K$, regular away from the supersingular places. It is used by [`CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet`](thm.html#CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet), which strengthens the conclusion by also bounding the pole order of $\omega$ at the supersingular places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf) :
    ∃ ω : Ω[ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
      (∀ v : AlgebraicCurve.Place K
          (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
        v ∉ ModularCurve.ssPlacesQExp K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p →
          v.IsRegularAt ω) ∧
      ModularCurve.diffQExp
          (ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω =
        ModularCurve.intSeriesC K pf := by sorry
