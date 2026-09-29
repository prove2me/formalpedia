-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isogenyData_forall_mem_iff_of_levelExt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isogenyData_forall_mem_iff_of_levelExt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/36fd3a94-bca3-509d-8c45-887f2e12a0ea
-- title:
--   Level-Nℓ extensions of the level structure come from isogeny lifts
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0 < a$ or $0 < b$, and for each height-one prime $v$ of the integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N \neq 0$, and let $\ell$ be a prime with $\ell \ne q$, $\ell \ne q'$ and $\ell \mid N$. Let $D$ be a fake elliptic curve of level $N$ over $\overline{\mathbb{Q}}$ and let $S$ be a set of points of $D$, i.e. of sections of `D.f` over the identity of $\operatorname{Spec} \overline{\mathbb{Q}}$, assumed to be closed under the group law `D.L` and inversion, to contain the identity section, to be stable under each `D.act x` for $x \in \Lambda$, to satisfy $\ell S \subseteq D.\mathrm{lev}$ and $D.\mathrm{lev} \subseteq \ell S$ (every point factoring through `D.lev` is $\ell P$ for some $P \in S$), and to satisfy that any $P \in S$ with $\ell P$ the identity factors through `D.lev`; here factoring through a morphism means the point's underlying morphism is a composite with it. Then there exist a fake elliptic curve $E$ of level $N$ over $\overline{\mathbb{Q}}$ together with an extra level structure $K$ of order $\ell$ on it (a term $u$ of `FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)`, with $E = u.1$), and morphisms $\varphi : E.A \to D.A$ over the base ($\varphi$ followed by `D.f` equals `E.f`) and $\psi : D.A \to E.A$ over the base, such that: $\varphi$ and $\psi$ are homomorphisms for the relative group laws on points with values in any test base $T \to \operatorname{Spec}\overline{\mathbb{Q}}$; $\varphi$ and $\psi$ commute with the $\Lambda$-actions, i.e. `E.act x` followed by $\varphi$ equals $\varphi$ followed by `D.act x`, and dually for $\psi$; $\psi \circ \varphi$ and $\varphi \circ \psi$ induce multiplication by $\ell$ on points of $E$ and of $D$ respectively; a point $P$ of $E$ has $\varphi(P)$ the identity precisely when $P$ factors through `u.2.levK`, so that $K$ is the kernel of $\varphi$; $\varphi$ carries points factoring through `E.lev` to points factoring through `D.lev`; and finally, for points $P$ over the identity of $\operatorname{Spec}\overline{\mathbb{Q}}$, one has $P \in S$ if and only if $\psi(P)$ factors through `E.lev`.
--
--   This is the surjectivity half of the moduli description of the degeneracy (isogeny) leg at $\ell$ for fake elliptic curves: every enlargement $S$ of the level-$N$ structure of $D$ to a $\Lambda$-stable group of points with $\ell S$ equal to the level structure is realised as the preimage of the level structure of a curve $E$ equipped with an extra level structure of order $\ell$ and level-$\ell$ isogeny data $\varphi, \psi$ to and from $D$. It feeds the counting of such lifts in [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isogenyData_forall_mem_iff_of_levelExt.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isogenyData_forall_mem_iff_of_levelExt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ℓ ∣ N)
    (D : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f))
    (hS : (∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ S → Q ∈ S → D.L.mul _ P Q ∈ S ∧ D.L.inv _ P ∈ S) ∧
      D.L.one _ ∈ S ∧
      (∀ (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f), P ∈ S → pushPt (D.act x) (D.act_over x) P ∈ S) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ S → FactorsThrough D.lev (nsmulPt D.L _ ℓ P)) ∧
      (∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, FactorsThrough D.lev Q → ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ S ∧ nsmulPt D.L _ ℓ P = Q) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ S → nsmulPt D.L _ ℓ P = D.L.one _ → FactorsThrough D.lev P)) :
    ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
      (φ : u.1.A ⟶ D.A) (hφ : φ ≫ D.f = u.1.f) (ψ : D.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = D.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t u.1.f),
        mapPt φ hφ (u.1.L.mul t P Q) = D.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t D.f),
        mapPt ψ hψ (D.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ D.act x) ∧ (∀ x : ↥Λ, D.act x ≫ ψ = ψ ≫ u.1.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
        mapPt ψ hψ (mapPt φ hφ P) = nsmulPt u.1.L t ℓ P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t D.f),
        mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt D.L t ℓ Q) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
        mapPt φ hφ P = D.L.one t ↔ FactorsThrough u.2.levK P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
        FactorsThrough u.1.lev P → FactorsThrough D.lev (mapPt φ hφ P)) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ S ↔ FactorsThrough u.1.lev (mapPt ψ hψ P)) := by sorry
