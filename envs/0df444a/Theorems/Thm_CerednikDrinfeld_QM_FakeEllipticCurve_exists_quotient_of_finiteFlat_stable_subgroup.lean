-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_of_finiteFlat_stable_subgroup
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_of_finiteFlat_stable_subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/21036696-6ba2-5a8c-a9ab-9b9c68b02b5b
-- title:
--   Quotient of a fake elliptic curve by a finite flat subgroup
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$, and a fake elliptic curve $E$ of type `FakeEllipticCurve Λ N S`, with structure morphism $E.f : E.A \to \operatorname{Spec} S$, relative group law $E.L$ and $\Lambda$-action $E.\mathrm{act}$. Let $\kappa : K \to E.A$ be a closed immersion such that $\kappa$ followed by $E.f$ is finite, flat and locally of finite presentation. Assume: for every $t : T \to \operatorname{Spec} S$ the unit point $E.L.\mathrm{one}\,t$ factors through $\kappa$ (i.e. equals $P_0$ followed by $\kappa$ for some $P_0 : T \to K$); points over $t$ factoring through $\kappa$ are closed under $E.L.\mathrm{mul}$ and $E.L.\mathrm{inv}$; they are preserved by composing with $E.\mathrm{act}\,x$ for every $x \in \Lambda$; and, for some $n > 0$, every such point satisfies $n\cdot P = E.L.\mathrm{one}\,t$ in the sense of `nsmulPt`. Assume also $1 \in \Lambda$. Then there exist a scheme $A'$ with $f' : A' \to \operatorname{Spec} S$, a relative group law $L'$ on $f'$, maps $\mathrm{act}' : \Lambda \to \operatorname{End}(A')$ over $f'$, morphisms $p : E.A \to A'$ over $S$ and $\psi : A' \to E.A$ over $S$, and a proof $w$ that $\mathrm{pullback.snd}(\kappa \circ E.f, E.f)$ followed by $p$ equals $E.L.\mathrm{action}\,\kappa$ followed by $p$, such that: $L'$ is commutative; $f'$ satisfies `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a group law existing); every fibre of $f'$ has topological Krull dimension $2$; $\mathrm{act}'$ is homomorphic on points, sends $1$ to $\mathbb{1}_{A'}$, is anti-multiplicative ($\mathrm{act}'(xy) = \mathrm{act}'\,y$ followed by $\mathrm{act}'\,x$) and additive on points, exactly in the shapes of the corresponding `FakeEllipticCurve` fields; $p$ and $\psi$ are homomorphisms on points and $\Lambda$-equivariant ($E.\mathrm{act}\,x \circ p = p \circ \mathrm{act}'\,x$ and $\psi \circ \mathrm{act}'\,x = E.\mathrm{act}\,x \circ \psi$ in diagrammatic order); whenever $(n:\mathbb{Q})$ lies in $\Lambda$, $p$ followed by $\psi$ is $E.\mathrm{act}\,n$ and $\psi$ followed by $p$ is $\mathrm{act}'\,n$; on points, $\psi \circ p$ and $p \circ \psi$ are multiplication by $n$ for $E.L$ and for $L'$ respectively; $p$ is finite, flat, locally of finite presentation and surjective, with $p.\mathrm{finrank}\,y$ equal to the rank of $\kappa \circ E.f$ at $f'.\mathrm{base}\,y$; a point $P$ over $t$ maps to $L'.\mathrm{one}\,t$ under $p$ if and only if $P$ factors through $\kappa$; $p$ has the universal property that every $\varphi : E.A \to X$ over $S$ which is a homomorphism to a relative group law $L_X$ and kills all points factoring through $\kappa$ factors through $p$ by a unique morphism over the base which is again a homomorphism on points; and finally the square formed by $\mathrm{pullback.snd}$, $E.L.\mathrm{action}\,\kappa$ and the two copies of $p$ is a pullback and $p$ is a coequaliser, $\mathrm{Cofork.of}\pi\,p\,w$ being a colimit.
--
--   This is the construction of the quotient of a fake (false) elliptic curve by a finite flat $\Lambda$-stable subgroup scheme killed by $n$: the quotient carries all the data of a fake elliptic curve except the trace condition and the level-$N$ structure, together with the dual map $\psi$ with $p\psi = [n]$, the identification of the kernel of $p$ with $K$, the universal property of the quotient, and the presentation of $p$ as the coequaliser of the action groupoid $K \times_S E.A \rightrightarrows E.A$ (so that base change and further descent apply). It is used in the construction of level isogenies of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_of_finiteFlat_stable_subgroup.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_of_finiteFlat_stable_subgroup
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) {K : Scheme.{u}} (κ : K ⟶ E.A) [IsClosedImmersion κ]
    [IsFinite (κ ≫ E.f)] [Flat (κ ≫ E.f)] [LocallyOfFinitePresentation (κ ≫ E.f)]
    (hK_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough κ (E.L.one t))
    (hK_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      FactorsThrough κ P → FactorsThrough κ Q → FactorsThrough κ (E.L.mul t P Q) ∧ FactorsThrough κ (E.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough κ P → FactorsThrough κ (pushPt (E.act x) (E.act_over x) P))
    (n : ℕ) (hn : 0 < n) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (hK_tors : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough κ P → nsmulPt E.L t n P = E.L.one t) :
    ∃ (A' : Scheme.{u}) (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
      (act' : ↥Λ → (A' ⟶ A')) (act'_over : ∀ x : ↥Λ, act' x ≫ f' = f')
      (p : E.A ⟶ A') (hp : p ≫ f' = E.f) (ψ : A' ⟶ E.A) (hψ : ψ ≫ E.f = f')
      (w : pullback.snd (κ ≫ E.f) E.f ≫ p = E.L.action κ ≫ p),

      L'.IsCommutative ∧ AbelianSchemePropertyBundle S f' ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f'.base ⁻¹' {s}) = 2) ∧

      (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
        pushPt (act' x) (act'_over x) (L'.mul t P Q) =
          L'.mul t (pushPt (act' x) (act'_over x) P) (pushPt (act' x) (act'_over x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act' ⟨1, h⟩ = 𝟙 A') ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act' y ≫ act' x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
        pushPt (act' (x + y)) (act'_over (x + y)) P =
          L'.mul t (pushPt (act' x) (act'_over x) P) (pushPt (act' y) (act'_over y) P)) ∧

      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
        mapPt ψ hψ (L'.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ act' x) ∧ (∀ x : ↥Λ, act' x ≫ ψ = ψ ≫ E.act x) ∧
      (∀ hn_mem : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
        p ≫ ψ = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn_mem⟩ ∧ ψ ≫ p = act' ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn_mem⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        mapPt ψ hψ (mapPt p hp P) = nsmulPt E.L t n P) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t f'),
        mapPt p hp (mapPt ψ hψ Q) = nsmulPt L' t n Q) ∧

      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ y : ↥A', p.finrank y = (κ ≫ E.f).finrank (f'.base y)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        mapPt p hp P = L'.one t ↔ FactorsThrough κ P) ∧

      (∀ {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of S)} (LX : RelativeGroupLaw S gX)
        (φ : E.A ⟶ X) (hφ : φ ≫ gX = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough κ P → mapPt φ hφ P = LX.one t) →
        ∃! χ : SchemeHomOver f' gX, p ≫ χ.1 = φ ∧
          ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
            mapPt χ.1 χ.2 (L'.mul t P Q) = LX.mul t (mapPt χ.1 χ.2 P) (mapPt χ.1 χ.2 Q)) ∧

      CategoryTheory.IsPullback (pullback.snd (κ ≫ E.f) E.f) (E.L.action κ) p p ∧
        Nonempty (IsColimit (Cofork.ofπ p w)) := by sorry
