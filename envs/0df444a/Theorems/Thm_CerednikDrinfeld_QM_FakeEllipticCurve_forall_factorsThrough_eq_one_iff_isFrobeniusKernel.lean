-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_eq_one_iff_isFrobeniusKernel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_eq_one_iff_isFrobeniusKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/496784d7-3b01-5067-a0de-f7478741eaeb
-- title:
--   Extra level at ℓ has no k-points iff it is ker F
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ and a natural number $N$. Let $k$ be an algebraically closed field of characteristic a prime $\ell$ with $\ell \nmid N$, and assume $\Lambda$ is a maximal order, i.e. an order that contains no strictly larger order. Let $q,q'$ be primes such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($a>0$ or $b>0$) and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; assume $\ell \ne q$ and $\ell \ne q'$. Let $E$ and $E_\ell$ be fake elliptic curves over $k$ for $(\Lambda,N)$, let $D$ be a Frobenius–Verschiebung datum for $\ell$ relating them (exhibiting $E_\ell$ as the pullback of $E$ along the $\ell$-power Frobenius of $k$ via $\mathrm{pr}$, compatibly with the relative group laws, the $\Lambda$-actions and the level structures, and providing morphisms $F : E \to E_\ell$ and $V : E_\ell \to E$ over $k$ that are homomorphisms for the relative group laws, commute with the $\Lambda$-actions and preserve the level structures, together with the remaining compatibilities of that structure). Let $K$ be an extra level at $\ell$ on $E$: a scheme with a closed immersion $\mathrm{lev}_K$ into $E$ whose set of factoring points is stable under multiplication, inversion, the $\Lambda$-action, contains the identity section, consists of $\ell$-torsion, meets the $N$-level structure only in the identity, and whose structure morphism to $\mathrm{Spec}\,k$ is finite, flat and locally of finite presentation of rank $\ell^2$ with geometric fibres isomorphic to $(\mathbb Z/\ell)^2$. The assertion is an equivalence: every $k$-point of $E$ (a morphism $\mathrm{Spec}\,k \to E$ over the identity of $\mathrm{Spec}\,k$) that factors through $\mathrm{lev}_K$ equals the identity section, if and only if the pair $\langle E,K\rangle$ satisfies `IsFrobeniusKernel` with respect to $D$, that is: for every scheme $T$, every morphism $t : T \to \mathrm{Spec}\,k$ and every $T$-point $P$ of $E$ over $t$, $P$ factors through $\mathrm{lev}_K$ if and only if $P$ followed by $F$ is the identity section of $E_\ell$ over $t$.
--
--   This is the functorial form of Morita's criterion in the inseparable/separable dichotomy for level-$\ell$ structures on fake elliptic curves in characteristic $\ell$: triviality of the $k$-points of a rank-$\ell^2$ $\Lambda$-stable subgroup $K \subseteq E[\ell]$ forces $K$ to be the kernel of the relative Frobenius, as a subgroup functor on all test schemes. It is used in the two branches of that dichotomy, namely in the construction of a Frobenius–Verschiebung datum when some nontrivial $k$-point exists, and in the identification of the quotient with the Frobenius twist when none does.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_eq_one_iff_isFrobeniusKernel.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_eq_one_iff_isFrobeniusKernel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) :
    (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
        FactorsThrough K.levK P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) ↔
      IsFrobeniusKernel (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) D := by sorry
