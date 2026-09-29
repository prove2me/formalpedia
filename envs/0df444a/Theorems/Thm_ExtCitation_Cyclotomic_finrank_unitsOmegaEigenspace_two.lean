-- Prove2me | Theorems.Thm_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two
-- name    : ExtCitation.Cyclotomic.finrank_unitsOmegaEigenspace_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/7b28b6a9-acc0-5a64-927c-aa12e5345936
-- title:
--   One-dimensionality of the ω²-eigenspace of the cyclotomic units
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $K = \mathbb{Q}(\zeta_p)$ be realised as `CyclotomicField p ℚ` with ring of integers $\mathcal{O}_K$. Write $E = \mathcal{O}_K^\times$, viewed additively, and consider $M =$ `ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)`, the quotient of this additive group by the subgroup of $p$-multiples, i.e. $E/E^p$, which is a module over $\mathbb{Z}/p$. The group $(\mathbb{Z}/p)^\times$ acts $\mathbb{Z}/p$-linearly on $M$ through the monoid homomorphism `unitsGalAction p`, obtained by composing the cyclotomic Galois action `clRingAction p (CyclotomicField p ℚ)` with the induced action `unitsEndHom` on units modulo $p$-th powers. The submodule `unitsOmegaEigenspace p 2` consists of those $a \in M$ satisfying $\rho(d)\,a = (d)^2 \cdot a$ in $M$ for every $d \in (\mathbb{Z}/p)^\times$, where $\rho =$ `unitsGalAction p` and $(d)^2$ is the square of the image of $d$ in $\mathbb{Z}/p$. The theorem asserts that this eigenspace has $\mathbb{Z}/p$-dimension exactly $1$, as measured by `Module.finrank`.
--
--   This is the eigenspace bookkeeping for the even character $\omega^2$ of $(\mathbb{Z}/p)^\times$ acting on the global units of $\mathbb{Q}(\zeta_p)$ modulo $p$-th powers; the hypothesis $5 \le p$ excludes the case $p = 3$, where $\omega^2$ is the trivial character and the eigenspace vanishes. It is used in the Thaine-type relation [`ExtCitation.Cyclotomic.thaine_relation_plusField`](thm.html#ExtCitation.Cyclotomic.thaine_relation_plusField) and in [`ExtCitation.Cyclotomic.unitsOmegaEigenvector_two_eq_zero_of_local_pow`](thm.html#ExtCitation.Cyclotomic.unitsOmegaEigenvector_two_eq_zero_of_local_pow), where a single explicit cyclotomic unit is shown to span this line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean

import Definitions.Def_ExtCitation_CyclotomicUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ExtCitation.Cyclotomic
open NumberField JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]

theorem finrank_unitsOmegaEigenspace_two (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (unitsOmegaEigenspace p 2) = 1 := by sorry
