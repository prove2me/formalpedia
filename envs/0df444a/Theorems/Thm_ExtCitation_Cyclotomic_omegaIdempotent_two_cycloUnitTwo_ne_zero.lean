-- Prove2me | Theorems.Thm_ExtCitation_Cyclotomic_omegaIdempotent_two_cycloUnitTwo_ne_zero
-- name    : ExtCitation.Cyclotomic.omegaIdempotent_two_cycloUnitTwo_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/f20cf51d-b7f0-5228-b8e7-303d62f2bb86
-- title:
--   Nonvanishing of the ω²-component of 1+ζₚ
-- statement:
--   Let $p$ be a prime with $p \ge 5$, and write $K = \mathbb{Q}(\zeta_p)$ for the $p$-th cyclotomic field `CyclotomicField p ℚ` with ring of integers $\mathcal{O}_K$. Let $\zeta \in \mathcal{O}_K$ be an element whose image in $K$ is a primitive $p$-th root of unity, and let $c_2 \in \mathcal{O}_K^{\times}$ be a unit whose underlying element of $\mathcal{O}_K$ equals $1 + \zeta$. Consider the group $E = \mathcal{O}_K^{\times}$ written additively and its quotient $E/pE$ by the subgroup of $p$-th multiples (multiplicatively, $\mathcal{O}_K^{\times}/(\mathcal{O}_K^{\times})^p$), a $\mathbb{Z}/p$-module; `ModP.proj` denotes the quotient map. The action `unitsGalAction p` sends $d \in (\mathbb{Z}/p)^{\times}$ to the $\mathbb{Z}/p$-linear endomorphism of $E/pE$ induced by the ring automorphism $\sigma_d$ of $\mathcal{O}_K$ corresponding to $d$ under the cyclotomic identification of $(\mathbb{Z}/p)^{\times}$ with the Galois group. The assertion is that the operator $$e_2 = (\#(\mathbb{Z}/p)^{\times})^{-1} \sum_{d \in (\mathbb{Z}/p)^{\times}} (d^{2})^{-1}\, \sigma_d,$$ computed in $\mathbb{Z}/p$ coefficients, does not annihilate the class of $c_2$ in $E/pE$.
--
--   This is the even-index cyclotomic-unit computation of Herbrand–Ribet type: the unit $1 + \zeta_p$ has nonzero $\omega^2$-component in $\mathcal{O}_K^{\times}/(\mathcal{O}_K^{\times})^p$, with no exceptional prime beyond $p = 3$, which the hypothesis $p \ge 5$ excludes. It supplies the eigen-unit used in the Thaine relation [`ExtCitation.Cyclotomic.thaine_relation_plusField`](thm.html#ExtCitation.Cyclotomic.thaine_relation_plusField) and, through it, in the vanishing statement [`ExtCitation.Cyclotomic.clGalAction_omegaEigenspace_two_eq_bot`](thm.html#ExtCitation.Cyclotomic.clGalAction_omegaEigenspace_two_eq_bot) for the $\omega^2$-eigenspace of the $p$-torsion of the class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_Cyclotomic_omegaIdempotent_two_cycloUnitTwo_ne_zero.lean

import Definitions.Def_ExtCitation_CyclotomicUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace ExtCitation.Cyclotomic
open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]

theorem omegaIdempotent_two_cycloUnitTwo_ne_zero (hp5 : 5 ≤ p)
    (ζ : 𝓞 (CyclotomicField p ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
    (c₂ : (𝓞 (CyclotomicField p ℚ))ˣ) (hc : (c₂ : 𝓞 (CyclotomicField p ℚ)) = 1 + ζ) :
    omegaIdempotent p (unitsGalAction p) 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)
          (Additive.ofMul c₂)) ≠ 0 := by sorry
