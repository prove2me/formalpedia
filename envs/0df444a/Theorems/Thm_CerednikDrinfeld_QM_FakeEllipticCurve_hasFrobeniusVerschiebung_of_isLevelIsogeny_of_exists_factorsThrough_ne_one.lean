-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/af65e441-2f83-50e9-a7fd-9196ff18d100
-- title:
--   Level-ℓ quotient with a nontrivial point: E is Frobenius twist of d
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ and $N \in \mathbb{N}$. Let $k$ be an algebraically closed field of characteristic $\ell$ with $\ell$ prime and $\ell \nmid N$, let $\Lambda$ be a maximal order (an order maximal among the orders containing it), and let $q,q'$ be primes such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; assume $\ell \neq q$ and $\ell \neq q'$. Let $E, E_\ell$ be fake elliptic curves over $k$ with $\Lambda$-action and level-$N$ data, let $D$ be a Frobenius–Verschiebung datum for $(\ell, E, E_\ell)$ — an identification of $E_\ell$ with the base change of $E$ along the Frobenius of $k$, compatible with group law, $\Lambda$-action and level structure, together with maps $F : E.A \to E_\ell.A$ and $V : E_\ell.A \to E.A$ over $k$ that are homomorphisms for the relative group laws, commute with the $\Lambda$-actions, and preserve the level-$N$ structures. Let $K$ be an extra level-$\ell$ structure on $E$: a closed immersion $\mathrm{levK} : K \to E.A$ whose points are stable under multiplication and inversion, contain the identity section, are killed by $\ell$, are stable under $\Lambda$, meet the level-$N$ structure only in the identity, and which is finite, flat and locally of finite presentation over $k$ of rank $\ell^2$. Let $d$ be a fake elliptic curve and assume $\mathrm{IsLevelIsogeny}$ for $(\ell, (E,K), d)$: there are $\varphi : E.A \to d.A$ and $\psi : d.A \to E.A$ over $k$, homomorphisms for the relative group laws, commuting with the $\Lambda$-actions, with $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ equal to the action of $\ell$ whenever $\ell \in \Lambda$, such that a point is annihilated by $\varphi$ exactly when it factors through $\mathrm{levK}$, and $\varphi$ carries level-$N$ points to level-$N$ points. Assume finally that there is a $k$-point of $E.A$ (a section over the identity of $\mathrm{Spec}\,k$) that factors through $\mathrm{levK}$ and differs from the identity section. Then $\mathrm{HasFrobeniusVerschiebung}\ \ell\ d\ E$ holds, i.e. there exists a Frobenius–Verschiebung datum for $(\ell, d, E)$, exhibiting $E$ as the Frobenius twist of $d$.
--
--   This is the separable half of the characteristic-$\ell$ dichotomy for fake elliptic curves: when the extra level-$\ell$ subgroup has a nontrivial $k$-rational point, so that it is étale rather than the kernel of Frobenius, the quotient $d$ has $E$ as its Frobenius twist. Together with the inseparable half it classifies the reduced level-$\ell$ quotients, and it is used in the Čerednik–Drinfeld description of the Shimura curve model to compute the action of Frobenius on the correspondence attached to a supersingular point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_isLevelIsogeny_of_exists_factorsThrough_ne_one.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_isLevelIsogeny_of_exists_factorsThrough_ne_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) (d : FakeEllipticCurve Λ N k)
    (hd : IsLevelIsogeny ℓ (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) d)

    (hK : ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      FactorsThrough K.levK P ∧ P ≠ E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    FakeEllipticCurve.HasFrobeniusVerschiebung ℓ d E := by sorry
