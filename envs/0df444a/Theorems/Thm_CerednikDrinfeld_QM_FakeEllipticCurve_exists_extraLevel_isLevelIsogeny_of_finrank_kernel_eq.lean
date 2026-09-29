-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a6bda74c-953c-5ba8-a490-dce12cb10adc
-- title:
--   Kernel of an ℓ-isogeny as an extra level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $k$ be a field and $\ell$ a prime with $\ell \nmid N$, and suppose $\Lambda$ is an order, i.e. contains $1$, is closed under multiplication, has $\mathbb{Q}$-span all of $\mathbb{H}[\mathbb{Q},a,b]$ and is finitely generated. Let $E,E'$ be fake elliptic curves of level $N$ over $k$, and let $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ be morphisms over $\operatorname{Spec} k$ which, on points over every test scheme $T \to \operatorname{Spec} k$, are homomorphisms for the relative group laws, commute with the $\Lambda$-actions (in the form $E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $E'.\mathrm{act}\,x$, and symmetrically), and satisfy $\psi\varphi = [\ell]$ on points of $E$ and $\varphi\psi = [\ell]$ on points of $E'$; assume moreover that $\varphi$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $E'.\mathrm{lev}$. Write $Z$ for the pullback of $\varphi$ against the unit section of $E'$ over $\operatorname{Spec} k$, and assume the first projection of $Z$ followed by $E.f$ is finite, locally of finite presentation, of rank $\ell^2$ at every point of $\operatorname{Spec} k$, and that for every algebraically closed field $k'$ with a ring map $k \to k'$ in which $\ell \neq 0$ the set of points of $E$ over the associated geometric point factoring through that projection is in group-law-preserving bijection with $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$. The conclusion asserts the existence of an extra level $K$ at $\ell$ on $E$ — a closed immersion $K.\mathrm{levK}$ into $E.A$ whose points over any test scheme form a subgroup containing the unit, killed by $\ell$, stable under $\Lambda$ and meeting $E.\mathrm{lev}$ only in the unit, with $K.\mathrm{levK}$ followed by $E.f$ finite, flat, locally of finite presentation of rank $\ell^2$ and with geometric fibres $(\mathbb{Z}/\ell)^2$ — such that, over every test scheme, a point factors through $K.\mathrm{levK}$ precisely when $\varphi$ sends it to the unit, and such that `IsLevelIsogeny ℓ ⟨E, K⟩ E'` holds: there are $\Lambda$-equivariant homomorphisms between $E$ and $E'$ whose composites equal the actions of $\ell$ as morphisms whenever $\ell \in \Lambda$, whose kernel on points is exactly $K$, and which preserve the level-$N$ structures.
--
--   This is the kernel-packaging step for fake elliptic curves: given an $\ell$-isogeny with an $\ell$-cofactor together with the finiteness and rank data for its scheme-theoretic kernel, the kernel is recognised as an extra level at $\ell$ and the isogeny as the corresponding level-$\ell$ isogeny. It is the common engine behind the constructions of level-$\ell$ isogenies from Frobenius–Verschiebung data and the symmetry and flip statements for objects with extra level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (E E' : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f)
    (φ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (φ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) (ψ_act : ∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x)
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t ℓ Q)
    (φ_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P))

    (hfin : IsFinite (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f))
    (hlfp : LocallyOfFinitePresentation (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f))
    (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f).finrank s = ℓ ^ 2)
    (hfibre : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), (ℓ : k') ≠ 0 →
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k' sk) E.f // FactorsThrough (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1) P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k' sk) E.f) = E.L.mul (geomPoint k' sk) (e x) (e y)) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔ mapPt φ hφ P = E'.L.one t) ∧
      IsLevelIsogeny ℓ (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) E' := by sorry
