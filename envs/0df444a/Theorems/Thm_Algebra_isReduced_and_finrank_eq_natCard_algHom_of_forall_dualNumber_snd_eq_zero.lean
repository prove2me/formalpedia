-- Prove2me | Theorems.Thm_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
-- name    : Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/969af4b5-a5e6-525f-93c8-6fdee5a3ccea
-- title:
--   No dual-number points implies reduced, with rank the point count
-- statement:
--   Let $F$ be a field and $R$ a commutative ring which is an $F$-algebra, finite as an $F$-module, and let $\Omega$ be an algebraically closed field which is an $F$-algebra. Assume that for every $F$-algebra homomorphism $\varphi : R \to \Omega[\varepsilon]/(\varepsilon^2)$ into the dual numbers over $\Omega$ and every $r \in R$, the $\varepsilon$-component $(\varphi\,r).\mathrm{snd}$ vanishes; that is, $R$ admits no $\Omega$-valued point with a nonzero tangent vector. The conclusion is the conjunction of two assertions: first, $R$ is reduced, i.e. has no nonzero nilpotents; second, the dimension of $R$ as an $F$-vector space equals $\mathrm{Nat.card}$ of the type of $F$-algebra homomorphisms $R \to \Omega$, the number of $\Omega$-valued points of $R$ (with the usual convention that $\mathrm{Nat.card}$ is $0$ for an infinite type, and $\mathrm{Module.finrank}$ is $0$ when $R$ is not finite-dimensional, which here cannot occur). No separability or connectedness hypothesis is imposed, and $\Omega$ is not assumed to contain $F$ as anything beyond an algebra.
--
--   This is the étaleness criterion in the form needed downstream: vanishing of all $\Omega$-valued tangent vectors forces the finite $F$-algebra $R$ to be étale, hence reduced and of rank equal to its geometric point count. It is used in the study of the coordinate rings of modular curves at full level, in [`ModularCurve.FullLevel.isReduced_and_finrank_fractionRing_tensorProduct_levelModuliPackageAbs_eq_gamma0Pow`](thm.html#ModularCurve.FullLevel.isReduced_and_finrank_fractionRing_tensorProduct_levelModuliPackageAbs_eq_gamma0Pow) and its Diamond-operator companion, to convert a count of geometric points into a statement about dimension and reducedness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    (h : ∀ (φ : R →ₐ[F] DualNumber Ω) (r : R), (φ r).snd = 0) :
    IsReduced R ∧ Module.finrank F R = Nat.card (R →ₐ[F] Ω) := by sorry
