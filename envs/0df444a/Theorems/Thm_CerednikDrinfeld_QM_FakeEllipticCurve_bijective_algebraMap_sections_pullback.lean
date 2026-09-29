-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_bijective_algebraMap_sections_pullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.bijective_algebraMap_sections_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/89aa8429-e3a3-512d-9cd1-bd658603309b
-- title:
--   Universal bijectivity of T→Γ(A_T,𝒪) for fake elliptic curves
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb Q$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order, i.e. an order containing no order strictly larger than itself; let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\mathrm{star}(x)=\bar x\,\mu$ for all $x\in\Lambda$. Let $N\in\mathbb N$, let $S$ be a commutative ring, and let $E$ be a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ datum: in particular a scheme $A$ with structure morphism $f:A\to\operatorname{Spec} S$, a commutative relative group law on $f$, an abelian-scheme property bundle for $f$, all fibres of topological Krull dimension $2$, and an action of $\Lambda$ by $S$-morphisms compatible with the group law and with the trace condition. The conclusion is that for every commutative ring $T$ with an $S$-algebra structure, the structure map of the base change is bijective on global sections: the algebra map $T\to\Gamma(A\times_{\operatorname{Spec} S}\operatorname{Spec} T,\top)$, where the $T$-algebra structure on the global sections is the one induced by the second projection $A_T\to\operatorname{Spec} T$, is bijective.
--
--   This is the statement $\mathcal O_T\xrightarrow{\sim}f_{T*}\mathcal O_{A_T}$ on global sections, holding universally over all $S$-algebras $T$, for the abelian surface underlying a fake elliptic curve. It is the form in which the rigidity input is required by the construction of canonical polarisations on fake elliptic curves and by the local description of such curves over local and Noetherian bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_bijective_algebraMap_sections_pullback.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.bijective_algebraMap_sections_pullback
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) :
    ∀ (T : Type) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd E.f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback E.f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)) := by sorry
