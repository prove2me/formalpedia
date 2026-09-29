-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_subsingleton_HSucc_pullback_tensor_three_of_isCanonicalPol
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_subsingleton_HSucc_pullback_tensor_three_of_isCanonicalPol
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/571ba3c8-fd15-5f3f-ad26-5f16f522ae83
-- title:
--   Vanishing of higher Čech cohomology of L^{⊗ 3} on field fibres
-- statement:
--   Let $a,b$ be rationals, $\Lambda$ a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, $N$ a natural number, and $S$ a commutative ring. Let $E$ be a `FakeEllipticCurve` for $\Lambda$, $N$ over $S$, so in particular a scheme $E.A$ with a morphism $E.f : E.A \to \operatorname{Spec} S$ carrying a commutative relative group law $E.L$, fibres of topological Krull dimension $2$, and an action $E.act$ of $\Lambda$ by endomorphisms over $\operatorname{Spec} S$. Let $\mathrm{star} : \Lambda \to \Lambda$ be any map and $\mathcal{L}$ an object of $E.A$-modules satisfying `IsCanonicalPolData` for $E.f$, $E.L$, $E.act$, $E.act\_over$, $\mathrm{star}$. Let $K$ be a field with an $S$-algebra structure. The assertion is that the fibre product $P$ of $E.f$ with $\operatorname{Spec} K \to \operatorname{Spec} S$ admits an ordered affine cover $\mathcal{W}$, that is, a finite linearly ordered family of affine open subsets of $P$ with supremum $\top$, such that for every $i \in \mathbb{N}$ the group $\ker d^{i+1} / \operatorname{im} d^{i}$ of the alternating Čech complex associated with $\mathcal{W}$ and the presheaf of $K$-modules $U \mapsto \Gamma(\mathcal{M}, U)$ is a subsingleton, where $\mathcal{M}$ is the pullback along the first projection $P \to E.A$ of $\mathcal{L} \otimes \mathcal{L} \otimes \mathcal{L}$ and the $K$-structure comes from the second projection $P \to \operatorname{Spec} K$. In other words, the Čech cohomology of $(\mathcal{L}^{\otimes 3})_K$ on $\mathcal{W}$ vanishes in all degrees $\ge 1$.
--
--   This is the vanishing theorem for powers of a polarisation, in the form needed for the fibres of a fake elliptic curve: the cube of a canonical polarisation datum has no higher Čech cohomology on a suitable affine cover of any field-valued fibre. It is used in the proof that the global sections of $\mathcal{L}^{\otimes 3}$ on such a fibre form a finite projective module compatible with base change, which supplies the projective embedding used in the moduli-theoretic part of the Čerednik–Drinfel'd comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_subsingleton_HSucc_pullback_tensor_three_of_isCanonicalPol.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_subsingleton_HSucc_pullback_tensor_three_of_isCanonicalPol
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ) (𝓛 : E.A.Modules) (h𝓛 : E.IsCanonicalPol star 𝓛)
    (K : Type) [Field K] [Algebra S K] :
    ∃ 𝒲 : (Limits.pullback E.f (Scheme.TwoAffineOpenCover.specMap S K)).OrderedAffineCover, ∀ i : ℕ,
      Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd E.f (Scheme.TwoAffineOpenCover.specMap S K))
        ((Scheme.Modules.pullback (Limits.pullback.fst E.f (Scheme.TwoAffineOpenCover.specMap S K))).obj (𝓛 ⊗ 𝓛 ⊗ 𝓛))).HSucc 𝒲 i) := by sorry
