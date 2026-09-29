-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_closedImmersionBySections_tensor_three_of_isCanonicalPol_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.closedImmersionBySections_tensor_three_of_isCanonicalPol_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/4753fad0-8085-55eb-ac81-ac939f0e37bf
-- title:
--   Cube of a canonical polarisation: closed immersion with h⁰=36
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a Noetherian commutative ring $S$. Let $E$ be a `FakeEllipticCurve Λ N S`, so that in particular $E$ provides a scheme $E.A$ with a morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$, the bundle of properties (smooth, proper, connected fibres, a group law) packaged by `AbelianSchemePropertyBundle`, fibres of topological Krull dimension $2$, and an action of $\Lambda$ by endomorphisms over $S$ compatible with the group law and with traces on tangent spaces. Let $star : \Lambda \to \Lambda$ be a map and $\mathcal{L}$ a module on $E.A$ satisfying `E.IsCanonicalPol star 𝓛`, i.e. `IsCanonicalPolData` for $E.f$, $E.L$, the $\Lambda$-action and $star$: $\mathcal{L}$ is invertible, symmetric, its kernel is two-torsion, after base change to some faithfully flat $S$-algebra $S'$ every relative group law compatible with $E.L$ admits an invertible $\mathcal{L}_0$ with trivial kernel such that the pullback of $\mathcal{L}$ is locally on the base isomorphic to $\mathcal{L}_0 \otimes [-1]^*\mathcal{L}_0$, the space of sections on every geometric fibre is non-zero, and the Rosati compatibility with the action and $star$ holds. The conclusion is twofold. First, $\mathcal{L} \otimes \mathcal{L} \otimes \mathcal{L}$ satisfies `ClosedImmersionBySections` over $E.f$: for some $N'$ there are global sections $\sigma_0,\dots,\sigma_{N'}$ of the cube together with a morphism $E.A \to \operatorname{Proj}$ of the polynomial ring in $N'+1$ variables over $S$, lying over $E.f$, trivialising the cube on the preimage of each basic open $D(X_i)$ and satisfying $(X_j/X_i)\cdot\sigma_i = \sigma_j$ there, which is a closed immersion. Second, for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$, the $k$-dimension of the global sections of the pullback of $\mathcal{L} \otimes \mathcal{L} \otimes \mathcal{L}$ to the geometric fibre $E.A \times_{\operatorname{Spec} S} \operatorname{Spec} k$ equals $36$.
--
--   This is the passage from a fake elliptic curve with canonical polarisation datum to a polarised abelian surface with the cube of the polarisation, relatively very ample of degree datum $h^0 = 36$; the fibrewise statement is the Lefschetz very-ampleness criterion for $n \ge 3$ together with $\chi(\mathcal{L}^{\otimes 3}) = 3^2\chi(\mathcal{L}) = 36$. It is used in the construction of the packages attached to quaternionic multiplication structures with full level and $2$ invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_closedImmersionBySections_tensor_three_of_isCanonicalPol_of_isNoetherianRing.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.closedImmersionBySections_tensor_three_of_isCanonicalPol_of_isNoetherianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] [IsNoetherianRing S]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ) (𝓛 : E.A.Modules) (h𝓛 : E.IsCanonicalPol star 𝓛) :
    Scheme.Modules.ClosedImmersionBySections (𝓛 ⊗ 𝓛 ⊗ 𝓛) E.f ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), Scheme.Modules.geomFibreH0Finrank E.f (𝓛 ⊗ 𝓛 ⊗ 𝓛) k sk = 36 := by sorry
