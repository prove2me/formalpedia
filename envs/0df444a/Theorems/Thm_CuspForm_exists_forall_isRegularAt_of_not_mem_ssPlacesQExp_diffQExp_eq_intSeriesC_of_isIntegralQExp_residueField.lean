-- Prove2me | Theorems.Thm_CuspForm_exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField
-- name    : CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/8779602f-41f2-5bb8-b7c7-00f843db7dcf
-- title:
--   Weight-two cusp forms give differentials regular off supersingular places
-- statement:
--   Let $p$ be a prime and $M \ge 1$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under reduction along $(M/p) \mid M$ is trivial. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the content of `LiesOverPrime`), whose residue field $\kappa = \kappa_A$ is assumed of characteristic $p$, algebraically closed and a $\mathbb{Z}/p$-algebra. Let $f$ be a cusp form of weight $2$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}(2,\mathbb{Z})$ of the subgroup of $\Gamma_0(M)$ whose lower-right entry mod $M$ lies in $H$, and let $p_f$ be a power series over $\mathbb{Z}$ whose image in $\mathbb{C}[[q]]$ is the width-one $q$-expansion of $f$ at $\infty$. Put $H' =$ [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and let $F' \subseteq \kappa((q))$ be `qExpFunctionFieldC`, the subfield of $\kappa((q))$ generated over $\kappa$ by all quotients of coefficientwise reductions of integral $q$-expansions of two modular forms of equal weight on [`CohCarrier.GammaH (M / p) H'`](def/CohCarrier_Level.html#L133). The assertion is that there exists $\omega \in \Omega_{F'/\kappa}$ such that: (i) for every place $v$ of $F'$ over $\kappa$ — a proper valuation subring of $F'$ containing $\kappa$ and a principal ideal ring — which does not lie in `ssPlacesQExp`, i.e. for which it fails that the $j$-series `jqModC` is the image of an element $x \in F'$ with $v$ taking at $x$ a value $a \in \kappa$ belonging to the set `ssJSet` attached to $p$ (the supersingular values), the differential $\omega$ is regular at $v$, meaning $\omega = c \cdot d(t_v)$ for some $c$ in the valuation ring of $v$ and $t_v$ a uniformiser of $v$; and (ii) the image of $\omega$ under `diffQExp`, the $F'$-linear map $\Omega_{F'/\kappa} \to \kappa((q))$ lifting the derivation `qEuler` of $\kappa((q))$ restricted to $F'$, is the Laurent series obtained from $p_f$ by reducing its integer coefficients into $\kappa$.
--
--   This is the mod $p$ incarnation, over the residue field of a place of $\overline{\mathbb{Q}}$ above $p$, of the passage from a weight-two cusp form of level $M$ with $p \mid M$, $p^2 \nmid M$ to a differential on the modular curve of level $M/p$ in characteristic $p$, regular away from the supersingular points; only integrality of the $q$-expansion at $\infty$ is assumed. It feeds the level-lowering step, where such differentials are compared with the $q$-expansions coming from the two degeneracy maps at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥A)]
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf) :
    ∃ ω : Ω[ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A)
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄(IsLocalRing.ResidueField ↥A)],
      (∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥A)
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A)
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
        v ∉ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥A)
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p →
          v.IsRegularAt ω) ∧
      ModularCurve.diffQExp
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A)
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω =
        ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) pf := by sorry
