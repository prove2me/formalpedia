-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_frobeniusVerschiebungData
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_frobeniusVerschiebungData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/0a4b95c0-33e0-5d78-bdbc-349e6430620e
-- title:
--   Kernel of Verschiebung as an extra level at ℓ
-- statement:
--   Let $a,b\in\mathbb Q$, let $\Lambda$ be a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, let $N$ be a natural number, let $k$ be an algebraically closed field, and let $\ell$ be a prime with $k$ of characteristic $\ell$ and $\ell\nmid N$. Assume $\Lambda$ is a maximal order (an order, and maximal among orders containing it), and that for primes $q,q'$ the algebra $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and ramified exactly at $q,q'$, in the sense that the completion at a finite place $v$ of $\mathbb Q$ is a division algebra precisely when $v$ divides $q$ or $q'$; assume $\ell\ne q$ and $\ell\ne q'$. Let $E,E_\ell$ be fake elliptic curves over $k$ with $\Lambda$-action and level-$N$ structure, and let $D$ be a Frobenius–Verschiebung datum for $\ell$ relating $E$ and $E_\ell$, in particular providing $F:E.A\to E_\ell.A$ and $V:E_\ell.A\to E.A$ over $\operatorname{Spec}k$ compatible with the group laws, the $\Lambda$-actions and the level structures. Then there exists an extra level $K$ at $\ell$ on $E_\ell$ — a closed immersion $K.\mathrm{levK}$ into $E_\ell.A$, stable under the group law, inversion and $\Lambda$, killed by $\ell$, meeting the level-$N$ structure only in the identity, finite, flat and of finite presentation of rank $\ell^2$ over the base, with geometric fibres isomorphic to $\mathbb Z/\ell\times\mathbb Z/\ell$ where $\ell$ is invertible — such that for every scheme $T$, every $t:T\to\operatorname{Spec}k$ and every $T$-point $P$ of $E_\ell$ over $t$, $P$ factors through $K.\mathrm{levK}$ if and only if $V\circ P$ is the identity section, and such that $\ell$ is a level isogeny from $(E_\ell,K)$ to $E$: there are maps in both directions over the base, compatible with the group laws and the $\Lambda$-actions, composing to the action of $\ell$ on either side when $\ell\in\Lambda$, whose first map has kernel exactly the points factoring through $K.\mathrm{levK}$ and carries the level-$N$ structure of $E_\ell$ into that of $E$.
--
--   This packages the scheme-theoretic kernel of the Verschiebung $V:E^{(\ell)}\to E$ of a fake elliptic curve in characteristic $\ell$ as an extra level structure at $\ell$, and exhibits $E$ as the corresponding level-$\ell$ quotient of $(E^{(\ell)},\ker V)$. It feeds the inseparable half of the Eichler–Shimura congruence for the Shimura curve $X_0^{qq'}(N)$ at a good prime $\ell$, via `iso_frobeniusTwist_frobeniusTwist_of_forall_nsmulPt_eq_one`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_frobeniusVerschiebungData.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_frobeniusVerschiebungData
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ) :
    ∃ K : Eℓ.ExtraLevel ℓ,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t Eℓ.f),
        FactorsThrough K.levK P ↔ mapPt D.V D.V_over P = E.L.one t) ∧
      IsLevelIsogeny ℓ (⟨Eℓ, K⟩ : WithExtraLevel Λ N ℓ k) E := by sorry
