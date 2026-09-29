-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_subsingleton_HSucc_pullback_tensor_four_of_isCanonicalPol
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_subsingleton_HSucc_pullback_tensor_four_of_isCanonicalPol
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a0c67c31-de03-5120-931a-db370bb22383
-- title:
--   Vanishing of higher Čech cohomology of L^{⊗ 4} on field fibres
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative ring $S$. Let $E$ be a `FakeEllipticCurve Λ N S`, so in particular $E$ carries a scheme $E.A$, a morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, and an action of $\Lambda$ by endomorphisms over $S$. Let $\mathrm{star} : \Lambda \to \Lambda$ be any self-map of $\Lambda$, let $\mathcal{L}$ be a module on $E.A$, and assume `IsCanonicalPolData E.f E.L E.act E.act_over star 𝓛`. Let $K$ be a field with an $S$-algebra structure. The assertion is that the base change $\operatorname{pullback}(E.f, \operatorname{Spec}(S \to K))$ admits an ordered affine cover $\mathcal{W}$ — a finite linearly ordered family of affine opens with supremum $\top$ — such that for every $i \in \mathbb{N}$ the group $\ker d^{i+1}/\operatorname{im} d^{i}$ of the ordered Čech complex associated with $\mathcal{W}$ and the presheaf of sections of the pullback along the first projection of $\mathcal{L} \otimes \mathcal{L} \otimes \mathcal{L} \otimes \mathcal{L}$, regarded as $K$-modules via the second projection, is a subsingleton. Thus all Čech cohomology of $\mathcal{L}^{\otimes 4}_K$ in degrees $\geq 1$ vanishes for a suitable cover. The parameter $N$ enters only through the type of $E$.
--
--   This is the Čech form of the vanishing theorem for a high tensor power of a polarisation on an abelian surface, applied to the fourth power of the canonical polarisation of a fake elliptic curve after base change to an arbitrary field-valued point of the base. It feeds the computation of the space of global sections of $\mathcal{L}^{\otimes 4}$ over Noetherian base rings, namely [`CerednikDrinfeld.QM.FakeEllipticCurve.finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullback_tensor_four_of_isCanonicalPol_of_isNoetherianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullback_tensor_four_of_isCanonicalPol_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_subsingleton_HSucc_pullback_tensor_four_of_isCanonicalPol.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_subsingleton_HSucc_pullback_tensor_four_of_isCanonicalPol
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ) (𝓛 : E.A.Modules) (h𝓛 : E.IsCanonicalPol star 𝓛)
    (K : Type) [Field K] [Algebra S K] :
    ∃ 𝒲 : (Limits.pullback E.f (Scheme.TwoAffineOpenCover.specMap S K)).OrderedAffineCover, ∀ i : ℕ,
      Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd E.f (Scheme.TwoAffineOpenCover.specMap S K))
        ((Scheme.Modules.pullback (Limits.pullback.fst E.f (Scheme.TwoAffineOpenCover.specMap S K))).obj (𝓛 ⊗ 𝓛 ⊗ 𝓛 ⊗ 𝓛))).HSucc 𝒲 i) := by sorry
