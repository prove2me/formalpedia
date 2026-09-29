-- Prove2me | Theorems.Thm_CuspForm_exists_isInfReductionMap_range_eq_ssPolarDifferentials
-- name    : CuspForm.exists_isInfReductionMap_range_eq_ssPolarDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/a3408432-3472-5ae6-aa5a-1c4f167f918e
-- title:
--   Mod p two-cusp forms as supersingular-polar differentials
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ such that every unit mapping to $1$ under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ lies in $H$, and let $K$ be an algebraically closed field that is an algebra over $\mathbb{Z}/p$. Write $H'$ for the image [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246) of $H$ in $(\mathbb{Z}/(M/p))^\times$ and $\Gamma =$ [`CohCarrier.GammaH (M / p) H'`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the matrices of $\Gamma_0(M/p)$ whose diagonal unit lies in $H'$; write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the subfield of $K((q))$ generated over $K$ by the quotients of coefficientwise mod-$p$ reductions of integral $q$-expansions at $\infty$ of pairs of modular forms of equal weight on $\Gamma$ (denominator nonzero). Then there is a $K$-linear map $\rho$ from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374), the reduction modulo $p$ of the two-cusp lattice `twoCuspLattice M H 2 p ⊥` of weight-two cusp forms on [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) (the lattice containing all forms $f$ such that for every element $t$ of the Hecke ring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ at $p$ and every $n$, the $n$-th $q$-expansion coefficients of $tf$ and of the weight-two Atkin–Lehner slash $W$ of $tf$ lie in the trivial subring of $\mathbb{C}$), to the module $\Omega_{F/K}$ of Kähler differentials, such that: (i) [`ModularCurve.IsInfReductionMap K p M H hpM ρ`](def/ModularCurve_XHDifferentialsModL.html#L443) holds, i.e. for every weight-two cusp form $f$ on [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) in `twoCuspIntegralSet M H 2 p ⊥` and every integral $q$-expansion $p_f \in \mathbb{Z}[[q]]$ of $f$, the $q$-expansion `diffQExp` of $\rho(1 \otimes \bar f)$ equals the coefficientwise mod-$p$ reduction `intSeriesC K pf`; and (ii) the range of $\rho$ is exactly [`ModularCurve.ssPolarDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L35), the submodule of differentials that are regular at every place of $F/K$ outside the set of supersingular places `ssPlacesQExp K Γ p` and have a simple pole at each place in it.
--
--   This is the identification, on the component of the special fibre through the cusp $\infty$, of the reduction modulo $p$ of the two-cusp integral weight-two cusp forms on $\Gamma_{H'}(M/p) \cap \Gamma_0(p)$ with the differentials on $X_{H'}(M/p)$ over $K$ having at most simple poles, concentrated at the supersingular places; classically it comes from the Deligne–Rapoport model and the $q$-expansion principle. It is used downstream in the passage from these differentials to torsion in the Jacobian and to the dual of the Tate module of $J_{H}$ in the ordinary case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isInfReductionMap_range_eq_ssPolarDifferentials.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CuspForm.exists_isInfReductionMap_range_eq_ssPolarDifferentials
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K] :
    ∃ ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
      ModularCurve.IsInfReductionMap K p M H hpM ρ ∧
      LinearMap.range ρ =
        ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by sorry
