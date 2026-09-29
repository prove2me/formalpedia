-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_forall_geomFibreH0Finrank_tensor_pullback_act_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_forall_geomFibreH0Finrank_tensor_pullback_act_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/69c9c16c-40d1-5342-9909-680b4103252c
-- title:
--   Uniform bound on h⁰(L ⊗ i(βⱼ)^*L)
-- statement:
--   Fix primes $q$ and $q'$ with $q' \neq q$, and rationals $a, b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, let $\star : \Lambda \to \Lambda$ satisfy $\mu \cdot \star x = \bar{x} \mu$ for all $x \in \Lambda$, and let $\beta : \mathrm{Fin}\,4 \to \Lambda$ be such that every element of $\Lambda$ is uniquely an integral combination $\sum_j c_j \beta_j$. Let $d, m$ be natural numbers with $m \geq 3$. The conclusion asserts the existence of $e : \mathrm{Fin}\,4 \to \mathbb{N}$, depending only on these data, such that for every commutative ring $T$, every polarised abelian scheme $X'$ of relative dimension $2$, polarisation degree $d$ and level $m$ over $T$, every `QMStructure` $s$ for $(\Lambda, \star, \beta)$ on $X'$, every index $j$, every algebraically closed field $k$ and every ring homomorphism $sk : T \to k$, the $k$-dimension of the global sections of the pullback of $X'.\mathrm{pol} \otimes s.\mathrm{act}(\beta_j)^* X'.\mathrm{pol}$ to the geometric fibre determined by $sk$ is at most $e_j$.
--
--   This is the uniform-boundedness form of the degree computation for the line bundles $\mathcal L \otimes i(\beta_j)^*\mathcal L$ attached to a quaternionic multiplication structure on a polarised abelian surface; the bound is uniform in the base ring, in the abelian scheme and in the geometric point. It is used, together with the corresponding base-change input, in establishing the quasi-compactness of the locus cut out by the quaternionic multiplication conditions inside the scheme of actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_forall_geomFibreH0Finrank_tensor_pullback_act_le.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_forall_geomFibreH0Finrank_tensor_pullback_act_le
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m) :
    ∃ e : Fin (2 * 2) → ℕ,
      ∀ (T : Type) [CommRing T] (X' : PolarisedAbelianScheme 2 d m T) (s : QMStructure Λ star β X')
        (j : Fin (2 * 2)) (k : Type) [Field k] [IsAlgClosed k] (sk : T →+* k),
        Scheme.Modules.geomFibreH0Finrank X'.f
          (X'.pol ⊗ (Scheme.Modules.pullback (s.act (β j))).obj X'.pol) k sk ≤ e j := by sorry
