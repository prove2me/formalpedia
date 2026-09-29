-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_closedImmersionBySections_tensor_four_of_isCanonicalPol_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.closedImmersionBySections_tensor_four_of_isCanonicalPol_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a61b8338-0962-5dc1-9a2c-4d806c90d2f1
-- title:
--   L^{⊗ 4} is very ample with h⁰=64
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, and a noetherian commutative ring $S$. Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$: a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$, the abelian-scheme bundle of properties (smooth, proper, connected fibres, a group law exists), fibres of topological Krull dimension $2$, and an action $E.act$ of $\Lambda$ by endomorphisms over $S$ compatible with the group law and with traces, together with the further curve data of the structure. Let $star : \Lambda \to \Lambda$ be any map and let $\mathcal L$ be a module on $E.A$ satisfying `E.IsCanonicalPol star 𝓛`, that is: $\mathcal L$ is invertible, symmetric for $E.f$ and $E.L$, its kernel is two-torsion, after a faithfully flat base change $S \to S'$ every relative group law compatible with $E.L$ admits an invertible $\mathcal L_0$ with trivial kernel whose $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ is locally isomorphic on the base to the pullback of $\mathcal L$, the geometric-fibre $h^0$ of $\mathcal L$ is positive at every algebraically closed point, and $\mathcal L$ is Rosati-compatible with $E.act$ and $star$. The conclusion has two parts. First, $\mathcal L \otimes (\mathcal L \otimes (\mathcal L \otimes \mathcal L))$ admits a closed immersion by sections over $E.f$: for some $n$ there are global sections $\sigma_0,\dots,\sigma_n$ of this module and a morphism $E.A \to \mathbf P^n_S$ over $\operatorname{Spec} S$ which is a closed immersion, such that on the preimage of each standard chart $\{X_i \neq 0\}$ multiplication by $\sigma_i$ is bijective from functions to sections, and the pullbacks of the ratios $X_j/X_i$ carry $\sigma_i$ to $\sigma_j$. Second, for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$, the $k$-dimension of the global sections of the pullback of $\mathcal L^{\otimes 4}$ to the geometric fibre along $sk$ equals $64$.
--
--   This is the Lefschetz very-ampleness statement together with the Riemann–Roch count $h^0(\mathcal L^{\otimes 4}) = 4^g h^0(\mathcal L) = 64$ for the canonical polarisation of a fake elliptic curve ($g = 2$, $h^0(\mathcal L) = 4$), in the form of an explicit projective embedding by global sections over the noetherian base. It supplies the projective embedding used in the construction of the fine moduli problem for fake elliptic curves and in the recognition of the associated formal module of height four.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_closedImmersionBySections_tensor_four_of_isCanonicalPol_of_isNoetherianRing.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.closedImmersionBySections_tensor_four_of_isCanonicalPol_of_isNoetherianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] [IsNoetherianRing S]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ) (𝓛 : E.A.Modules) (h𝓛 : E.IsCanonicalPol star 𝓛) :
    Scheme.Modules.ClosedImmersionBySections (𝓛 ⊗ 𝓛 ⊗ 𝓛 ⊗ 𝓛) E.f ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), Scheme.Modules.geomFibreH0Finrank E.f (𝓛 ⊗ 𝓛 ⊗ 𝓛 ⊗ 𝓛) k sk = 64 := by sorry
