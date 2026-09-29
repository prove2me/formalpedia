-- Prove2me | Theorems.Thm_CuspForm_forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
-- name    : CuspForm.forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/7048b049-0257-502d-8fee-8cae49ebe19b
-- title:
--   Diamond operators preserve p-divisibility of q-coefficients
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbf Z/M)^\times$ be a subgroup containing every unit whose image under the reduction $(\mathbf Z/M)^\times \to (\mathbf Z/(M/p))^\times$ is trivial, and let $K$ be an algebraically closed field of characteristic $p$, regarded as a $\mathbf Z/p$-algebra. Further data: an Atkin–Lehner datum $W$ for $(M,p)$, that is a factorisation $M = p R$ together with integers $a,b$ satisfying $pa - Rb = 1$; a unit $e$ of $\mathbf Z/M$ whose image in $\mathbf Z/(M/p)$ satisfies $\bar e\, p = 1$; and the assumption that there exists a $K$-linear map $\rho$ from $K \otimes_{\mathbf Z/p} \mathrm{IntTwoCuspForms}\,M\,H\,p$ — the two-cusp lattice of weight-$2$ cusp forms on $\mathrm{GammaH}\,M\,H$ modulo the submodule cut out by `intIdeal p` — to the module of Kähler differentials over $K$ of the $q$-expansion function field $\mathrm{qExpFunctionFieldC}\,K\,(\mathrm{GammaH}\,(M/p)\,(\mathrm{infSubgroup}\,p\,M\,H))$, satisfying [`ModularCurve.IsInfReductionMap`](def/ModularCurve_XHDifferentialsModL.html#L443): for every $f$ in the two-cusp integral set at level $(M,H)$, weight $2$, prime $p$ and coefficient ring $\bot \subseteq \mathbf C$, and every power series $p_f$ over $\mathbf Z$ whose image in $\mathbf C$ is the $q$-expansion of $f$, the differential $q$-expansion of $\rho(1 \otimes \bar f)$ is the Laurent series attached to $p_f$ over $K$. Then for every unit $d$ of $\mathbf Z/M$ and every weight-$2$ cusp form $y$ on $\mathrm{GammaH}\,M\,H$ lying in the two-cusp lattice $\mathrm{twoCuspLattice}\,M\,H\,2\,p\,\bot$ all of whose $q$-coefficients are $p$ times an integer, all $q$-coefficients of the diamond translate $\mathrm{diamondLinH}\,2\,d\,y$ (slashing by a lift of $d$ to $\mathrm{SL}_2(\mathbf Z)$ when the stability condition `StableD` holds, and $0$ otherwise) are again $p$ times an integer.
--
--   This is the statement that the diamond operators $\langle d\rangle$ preserve divisibility by $p$ of the Fourier coefficients at $\infty$ of forms in the two-cusp integral lattice, in the case $p \parallel M$, obtained here from the diamond-equivariance of an $\infty$-reduction map together with injectivity of the differential $q$-expansion. It is used in the two-cusp comparison, by [`ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash`](thm.html#ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (hex : ∃ ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
      ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (d : (ZMod M)ˣ)
    (y : CuspForm (CohCarrier.GammaH M H) 2) (hy : y ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))
    (h0 : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑y) n = (p : ℂ) * m) :
    ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d y)) n = (p : ℂ) * m := by sorry
