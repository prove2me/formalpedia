-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPol_of_isCanonicalPol_pullback_of_injective_of_isLocalHom
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_isCanonicalPol_pullback_of_injective_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/decda1d0-9654-5690-96f5-adf69db006ec
-- title:
--   Canonicity of a polarisation datum descends along an injective local homomorphism
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders (any order containing it equals it), a map $\mathrm{star} : \Lambda \to \Lambda$, and $N \in \mathbb{N}$. Let $T$ be a noetherian local ring, $R$ a local ring, and $\varphi : T \to R$ an injective local ring homomorphism. Let $E_T$ be a fake elliptic curve over $T$ and $E$ one over $R$ (in the sense of the structure `FakeEllipticCurve`, carrying a relative commutative group law, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action and level structure), and let $g : E.A \to E_T.A$ be a morphism making the square formed by $g$, $E.f$, $E_T.f$ and $\operatorname{Spec}\varphi$ cartesian. Assume $g$ is compatible with the group laws, in the sense that for every scheme $X$, every $t' : X \to \operatorname{Spec} R$ and all $P,Q : X \to E.A$ over $t'$, the product $P +_{E} Q$ followed by $g$ is the $E_T$-product of $P$ followed by $g$ and $Q$ followed by $g$, taken over $t'$ followed by $\operatorname{Spec}\varphi$; and that $E.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $E_T.\mathrm{act}(x)$ for every $x \in \Lambda$. Let $\mathcal{M}_T$ and $\mathcal{M}_{0,T}$ be modules on $E_T.A$ which are invertible (each point has a neighbourhood on which the restriction is isomorphic to the unit sheaf of modules), with $\mathcal{M}_T$ satisfying `KernelIsTwoTorsion` for $E_T.f, E_T.L$ (for every ring $R'$, every $t : \operatorname{Spec} R' \to \operatorname{Spec} T$ and every point $x$ over $t$, the Mumford bundle of $\mathcal{M}_T$ restricted along the slice at $x$ is isomorphic to the unit object locally on the base if and only if $x + x$ is the unit section) and $\mathcal{M}_{0,T}$ satisfying `KernelTrivial` (the same local triviality forces $x$ to be the unit section). Assume further that over $R$ the pullback $g^{*}\mathcal{M}_T$ satisfies the predicate `IsCanonicalPolData` for $E.f$, $E.L$, the $\Lambda$-action of $E$ and $\mathrm{star}$, and that $g^{*}\mathcal{M}_T$ and $g^{*}\mathcal{M}_{0,T} \otimes [-1]^{*}g^{*}\mathcal{M}_{0,T}$, where $[-1]$ is the inversion morphism `negMor E.f E.L` of the group law of $E$, become isomorphic after restriction to $E.f^{-1}(U)$ for suitable open neighbourhoods $U$ of each point of $\operatorname{Spec} R$. Then $\mathcal{M}_T$ satisfies `IsCanonicalPolData` for $E_T.f$, $E_T.L$, the $\Lambda$-action of $E_T$ and $\mathrm{star}$.
--
--   This is the descent step which transfers canonicity of a polarisation datum on a fake elliptic curve from a cartesian base change $\operatorname{Spec} R \to \operatorname{Spec} T$ back to the noetherian local stage $T$, the injectivity of $\varphi$ guaranteeing that the relevant Zariski-local triviality loci in $\operatorname{Spec} T$ are everything. It is used in the construction of canonical polarisations on fake elliptic curves over local bases in the Čerednik–Drinfel'd part of the development, where the square-root datum is produced after a faithfully flat extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isCanonicalPol_of_isCanonicalPol_pullback_of_injective_of_isLocalHom.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPol_of_isCanonicalPol_pullback_of_injective_of_isLocalHom
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (star : ↥Λ → ↥Λ)
    (N : ℕ) {T R : Type} [CommRing T] [CommRing R] [IsLocalRing T] [IsNoetherianRing T] [IsLocalRing R]
    (φ : T →+* R) (hφ : Function.Injective φ) (hφl : IsLocalHom φ)
    (ET : FakeEllipticCurve Λ N T) (E : FakeEllipticCurve Λ N R) (g : E.A ⟶ ET.A)
    (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom φ)))
    (hlaw : ∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x)
    (𝓜T 𝓜₀T : ET.A.Modules) (hT : Scheme.Modules.IsInvertible 𝓜T) (h₀T : Scheme.Modules.IsInvertible 𝓜₀T)
    (hK : KernelIsTwoTorsion ET.f ET.L 𝓜T) (hK₀ : KernelTrivial ET.f ET.L 𝓜₀T)
    (hcan : E.IsCanonicalPol star ((Scheme.Modules.pullback g).obj 𝓜T))
    (hsq : LocIsoOnBase E.f ((Scheme.Modules.pullback g).obj 𝓜T)
      ((Scheme.Modules.pullback g).obj 𝓜₀T ⊗
        (Scheme.Modules.pullback (negMor E.f E.L)).obj ((Scheme.Modules.pullback g).obj 𝓜₀T))) :
    ET.IsCanonicalPol star 𝓜T := by sorry
