-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth
-- name    : AlgebraicGeometry.Polarisation.exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/f882516d-1f81-5dec-85db-06cf0733b530
-- title:
--   Kernel of 2n(1+ι(b^⋆)ι(b)) equals the stabiliser of L⊗ι(b)^*L
-- statement:
--   Let $K$ be an algebraically closed field, $f : A \to \operatorname{Spec} K$ a morphism of schemes carrying a relative group law $L$ (a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of $T$-points, natural in the base change) which is commutative, together with the bundle of properties asserting that $f$ is smooth, proper, has connected fibres and admits a relative group law, and suppose $f$ is smooth of relative dimension $g$. Let $\mathcal L$ and $\mathcal L_E$ be invertible $\mathcal O_A$-modules (locally isomorphic to the unit), let $n \in \mathbb N$ and assume $\mathcal L$ and $\mathcal L_E^{\otimes n}$ become isomorphic after pullback to the preimage of some open neighbourhood of each point of $\operatorname{Spec} K$; assume furthermore that $\mathcal L_E$ is symmetric in this local sense, i.e. $[-1]^*\mathcal L_E$ and $\mathcal L_E$ agree locally over the base, and that $\mathcal L_E$ satisfies the two-torsion condition: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $T$-point $x$, the restriction along $\mathrm{sliceAt}\,f\,x$ of the Mumford bundle $\Lambda(\mathcal L_E)$ is locally trivial over the base exactly when $x + x = 0$. Let $\iota : I \to (A \to A)$ be a family of endomorphisms over $\operatorname{Spec} K$ which are homomorphisms for $L$ on all test points, let $\star : I \to I$, and assume the Rosati compatibility: for each $b$, the pullbacks of $\Lambda(\mathcal L_E)$ along $1 \times \iota(b)$ and along $\iota(b^\star) \times 1$ on $A \times_{\operatorname{Spec} K} A$ agree locally over the base. Fix $b \in I$ and an endomorphism $\gamma$ of $A$ over $\operatorname{Spec} K$ acting on points by $\gamma(x) = 2n\cdot\bigl(x + \iota(b^\star)(\iota(b)(x))\bigr)$. Then for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $T$-point $x$ of $f$, the morphism underlying $x$ factors through the projection $\mathrm{endKer}\,\gamma \to A$ — where $\mathrm{endKer}\,\gamma$ is the fibre product of $\gamma$ with the identity section of $L$ — if and only if $x$ lies in the stabiliser of $\mathcal L \otimes \iota(b)^*\mathcal L$, that is, the pullback of $\mathcal L \otimes \iota(b)^*\mathcal L$ along translation by $x$ is locally isomorphic, over $\operatorname{Spec} R$, to its pullback along the first projection of $A \times_{\operatorname{Spec} K} \operatorname{Spec} R$.
--
--   This is the functor-of-points form of Mumford's identification of the stabiliser $K(\mathcal M)$ of an invertible sheaf $\mathcal M = \mathcal L \otimes \iota(b)^*\mathcal L$ with the kernel of the associated endomorphism, here $2n(1 + \iota(b^\star)\iota(b))$ computed through the Rosati involution. It supplies the hypothesis matching stabilisers with kernels in the Riemann–Roch degree count, and is used in the computation of the rank of $H^0$ on geometric fibres for quaternionic multiplication data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

theorem AlgebraicGeometry.Polarisation.exists_comp_endKerIncl_eq_iff_isInStabilizer_tensor_pullback_of_rosatiCompatible_of_smooth
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝓛 polE : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hpolE : Scheme.Modules.IsInvertible polE)
    (n : ℕ) (hn : LocIsoOnBase f 𝓛 (Scheme.Modules.tensorPow polE n))
    (hsym : IsSymmetric f L polE) (hK2 : KernelIsTwoTorsion f L polE)
    {I : Type} (ι : I → (A ⟶ A)) (hι : ∀ b : I, ι b ≫ f = f)
    (hιhom : ∀ (b : I) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (ι b) (hι b) (L.mul t P Q) = L.mul t (pushPt (ι b) (hι b) P) (pushPt (ι b) (hι b) Q))
    (star : I → I) (hRos : RosatiCompatible f L polE ι hι star)
    (b : I) (γ : A ⟶ A) (hγ : γ ≫ f = f)
    (hγpt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      pushPt γ hγ x = L.nsmul t (2 * n) (L.mul t x (pushPt (ι (star b)) (hι (star b)) (pushPt (ι b) (hι b) x)))) :
    ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ L.endKer ⟨γ, hγ⟩, x₀ ≫ L.endKerι ⟨γ, hγ⟩ = x.1) ↔
        L.IsInStabilizer (𝓛 ⊗ (Scheme.Modules.pullback (ι b)).obj 𝓛) t x := by sorry
