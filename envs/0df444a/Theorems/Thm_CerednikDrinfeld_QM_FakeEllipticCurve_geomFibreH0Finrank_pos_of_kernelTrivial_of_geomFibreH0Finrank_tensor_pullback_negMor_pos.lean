-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_geomFibreH0Finrank_pos_of_kernelTrivial_of_geomFibreH0Finrank_tensor_pullback_negMor_pos
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.geomFibreH0Finrank_pos_of_kernelTrivial_of_geomFibreH0Finrank_tensor_pullback_negMor_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/8f30c072-6518-53f2-8e63-f3ed01ed4142
-- title:
--   Fibrewise h⁰>0 from positivity for the symmetrisation
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, a commutative ring $S$, and $E$ a term of `FakeEllipticCurve Λ N S` (so $E$ provides a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, and an action of $\Lambda$ by endomorphisms over $S$ with the trace condition). Let $R$ be a commutative $S$-algebra, and write $A_R \to \operatorname{Spec} R$ for the second projection of the pullback of $E.f$ along $\operatorname{Spec}$ of $S \to R$, with first projection $\pi : A_R \to E.A$. Assume given a relative group law $L'$ on $A_R/\operatorname{Spec} R$ such that for every scheme $T$, every $t' : T \to \operatorname{Spec} R$ and all $T$-points $P,Q$ of $A_R$ over $t'$, the morphism underlying $L'.\mathrm{mul}\,t'\,P\,Q$ followed by $\pi$ agrees with the $E.L$-sum of $P$ followed by $\pi$ and $Q$ followed by $\pi$, taken over $t'$ followed by $\operatorname{Spec}$ of $S \to R$; that is, $\pi$ is a homomorphism of group laws. Let $\mathcal L$ be a module on $A_R$ which is invertible (locally on $A_R$, its restriction to an open is isomorphic to the unit module), and assume `KernelTrivial`: for every commutative ring $R'$, every $t : \operatorname{Spec} R' \to \operatorname{Spec} R$ and every section $x$ of $A_R$ over $t$, if the pullback along the slice at $x$ of the Mumford bundle $\mathrm{add}^*\mathcal L \otimes (\mathrm{pr}_1^*\mathcal L^\vee \otimes \mathrm{pr}_2^*\mathcal L^\vee)$ on $A_R\times_{\operatorname{Spec} R} A_R$ is, locally over points of $\operatorname{Spec} R'$, isomorphic to the unit module, then $x$ is the identity section $L'.\mathrm{one}\,t$. Assume finally that for every algebraically closed field $k$ and every ring homomorphism $R \to k$ the quantity `Scheme.Modules.geomFibreH0Finrank` of $\mathcal L \otimes \nu^*\mathcal L$ is positive, where $\nu =$ `negMor` is the inversion morphism of $L'$ at the identity section. Then for every algebraically closed field $k$ and every ring homomorphism $sk : R \to k$, the `geomFibreH0Finrank` of $A_R \to \operatorname{Spec} R$ at $\mathcal L$ with respect to $(k,sk)$ — the $k$-dimension of the global sections of the pullback of $\mathcal L$ to the geometric fibre $A_R \times_{\operatorname{Spec} R}\operatorname{Spec} k$ — is positive.
--
--   This is the descent of Mumford's criterion for a line bundle with trivial kernel on an abelian variety: over each geometric fibre, non-vanishing of $h^0$ for the symmetrisation $\mathcal L \otimes [-1]^*\mathcal L$ forces non-vanishing of $h^0$ for $\mathcal L$ itself. It supplies the fibrewise positivity input in the construction of canonical polarisation data on base changes and infinitesimal lifts of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_geomFibreH0Finrank_pos_of_kernelTrivial_of_geomFibreH0Finrank_tensor_pullback_negMor_pos.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.geomFibreH0Finrank_pos_of_kernelTrivial_of_geomFibreH0Finrank_tensor_pullback_negMor_pos
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [Algebra S R]
    (L' : RelativeGroupLaw R (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))))
    (hL' : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))),
        (L'.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hK : KernelTrivial (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L' 𝓛)
    (hpos : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k),
      0 < Scheme.Modules.geomFibreH0Finrank (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
        (𝓛 ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L')).obj 𝓛) k sk)
    (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k) :
    0 < Scheme.Modules.geomFibreH0Finrank (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) 𝓛 k sk := by sorry
