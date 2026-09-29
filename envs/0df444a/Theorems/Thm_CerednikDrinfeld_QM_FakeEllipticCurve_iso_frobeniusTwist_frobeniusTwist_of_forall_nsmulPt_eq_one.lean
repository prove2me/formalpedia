-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_frobeniusTwist_frobeniusTwist_of_forall_nsmulPt_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_frobeniusTwist_frobeniusTwist_of_forall_nsmulPt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/3827e0e9-e3ae-562b-93e2-4cf74c55f954
-- title:
--   Double Frobenius twist of a supersingular fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ and a natural number $N$. Let $k$ be an algebraically closed field of characteristic a prime $\ell$ with $\ell \nmid N$, let $\Lambda$ be a maximal order (an order maximal among orders under inclusion), and let $q,q'$ be primes such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the $v$-adic completion of $\mathbb H[\mathbb Q,a,b]$ is a division algebra exactly when $v$ contains $q$ or $q'$; assume $\ell \ne q$ and $\ell \ne q'$. Let $A$, $A_\ell$, $A_{\ell\ell}$ be fake elliptic curves over $k$ of level $N$ with $\Lambda$-action (schemes over $\operatorname{Spec} k$ carrying a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action compatible with the group law and the trace condition, and a level structure $\mathrm{lev}$), and let $D_1$ be Frobenius–Verschiebung data for the pair $(A,A_\ell)$ and $D_2$ for $(A_\ell,A_{\ell\ell})$. Assume that the only $k$-point $P$ of $A$ (section over the identity of $\operatorname{Spec} k$) with $\ell P$ equal to the identity section is the identity section itself, i.e. $A[\ell](k)=0$. Then $A_{\ell\ell}$ and $A$ are isomorphic as fake elliptic curves: there is an isomorphism of schemes $e : A_{\ell\ell} \cong A$ over $\operatorname{Spec} k$ which is a homomorphism for the group laws on points over every base, intertwines the two $\Lambda$-actions, and matches the level structures, in the sense that a point factors through the level morphism of $A_{\ell\ell}$ if and only if its image under $e$ factors through that of $A$.
--
--   This is the supersingular case of the statement that the square of Frobenius acts trivially on supersingular points of the reduction of the Shimura curve attached to $\Lambda$, the moduli-theoretic input to the Eichler–Shimura congruence relation at $\ell$ for $X_0^{qq'}(N)$. It is used in the computation of the correspondence induced by Frobenius on the reduction of the Shimura curve model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_frobeniusTwist_frobeniusTwist_of_forall_nsmulPt_eq_one.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_frobeniusTwist_frobeniusTwist_of_forall_nsmulPt_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (A Aℓ Aℓℓ : FakeEllipticCurve Λ N k)
    (D₁ : FrobeniusVerschiebungData ℓ A Aℓ) (D₂ : FrobeniusVerschiebungData ℓ Aℓ Aℓℓ)

    (hss : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) A.f,
      nsmulPt A.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = A.L.one (𝟙 (Spec (CommRingCat.of k))) →
        P = A.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    FakeEllipticCurve.Iso Aℓℓ A := by sorry
