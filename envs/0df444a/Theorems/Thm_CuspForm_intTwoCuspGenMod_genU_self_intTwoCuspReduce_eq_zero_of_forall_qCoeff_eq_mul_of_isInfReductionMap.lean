-- Prove2me | Theorems.Thm_CuspForm_intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap
-- name    : CuspForm.intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/9770701d-29d6-5d88-95b4-2e7021f6b931
-- title:
--   Uₚ kills reductions of p-divisible two-cusp forms
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit $u$ whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Let $K$ be an algebraically closed field that is an algebra over $\mathbb{Z}/p$, and $S$ a set of natural numbers. Let $\rho$ be a $K$-linear map from $K \otimes_{\mathbb{Z}/p} \mathtt{IntTwoCuspForms}\,M\,H\,p$, the quotient of the two-cusp lattice `twoCuspLattice M H 2 p ⊥` by `intIdeal p • ⊤`, to the Kähler differentials $\Omega$ of the $q$-expansion function field `qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))` over $K$, where `infSubgroup` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$; assume [`ModularCurve.IsInfReductionMap K p M H hpM ρ`](def/ModularCurve_XHDifferentialsModL.html#L443), i.e. for every weight-$2$ cusp form $f$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) lying in the two-cusp integral set at $p$ over the subring $\bot \subseteq \mathbb{C}$ and every integral power series $p_f$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $f$, the series `diffQExp` of $\rho(1 \otimes \overline{f})$ is `intSeriesC K pf`. Let $y$ lie in `twoCuspLattice M H 2 p ⊥` and suppose every $q$-coefficient $a_n(y)$ is $p$ times an integer. Then the operator `intTwoCuspGenMod M H p S` attached to the generator `CohCarrier.Gen.U p _ hpM` annihilates the class of $y$ in $\mathtt{IntTwoCuspForms}\,M\,H\,p$.
--
--   This is the assertion, in Wiles's form, that a weight-$2$ form whose $q$-expansion at $\infty$ is divisible by $p$ has $U_p$-image trivial modulo $p$ once a reduction map onto the component through $\infty$ is available — the step "$\omega = 0$ on $\Sigma^{\mu}$ implies $U_p\omega = 0$ on $\Sigma^{\mathrm{\acute et}}$". It feeds [`ModularCurve.IsInfReductionMap.baseChange_genU_self_apply_eq_zero_of_apply_eq_zero`](thm.html#ModularCurve.IsInfReductionMap.baseChange_genU_self_apply_eq_zero_of_apply_eq_zero), and through it the analysis of the two components of the mod-$p$ modular curve at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct ModularForm MatrixGroups

theorem CuspForm.intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K] (S : Set ℕ)
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)))
    (hy : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑(y : CuspForm (CohCarrier.GammaH M H) 2)) n = (p : ℂ) * m) :
    CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.U p Fact.out hpM) (CuspForm.intTwoCuspReduce M H p y) = 0 := by sorry
