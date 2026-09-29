-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_of_isPullback_of_injective_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.generates_annihilator_of_isPullback_of_injective_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/1da74d55-1c7e-5b66-aacb-26210735e3b2
-- title:
--   Full m-level conditions descend along an injective base change
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and primes $q,q'$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, and let $N,m\in\mathbb{N}$. Let $R'$ be a noetherian commutative ring in which the image of $m$ is a unit, $L$ a commutative ring, and $\varphi:R'\to L$ an injective ring homomorphism. Let $E'$ be a fake elliptic curve of level $N$ over $R'$ with $\Lambda$-action, and $P'$ a section of $E'.f$ over $\mathrm{id}_{\operatorname{Spec} R'}$ with $mP'$ equal to the identity section for the relative group law of $E'$. Let $E$ be a fake elliptic curve of level $N$ over $L$ and $g_L:E.A\to E'.A$ a morphism making $E.f$, $E'.f$ and $\operatorname{Spec}\varphi$ a cartesian square; assume $g_L$ is compatible with the group laws on points (for every scheme $T$, every $t':T\to\operatorname{Spec} L$ and all points $P,Q$ over $t'$, the product $P\cdot Q$ followed by $g_L$ is the product of $P$ followed by $g_L$ and $Q$ followed by $g_L$, taken over $t'$ followed by $\operatorname{Spec}\varphi$), that $E.\mathrm{act}\,x$ followed by $g_L$ equals $g_L$ followed by $E'.\mathrm{act}\,x$ for all $x\in\Lambda$, and that $P$ is a section of $E.f$ over $\mathrm{id}_{\operatorname{Spec} L}$ with $P$ followed by $g_L$ equal to $\operatorname{Spec}\varphi$ followed by $P'$. Assume finally that at every geometric point of $\operatorname{Spec} L$ (an algebraically closed field $k$ with a ring homomorphism $L\to k$) the map $x\mapsto x\cdot P$ from $\Lambda$ to the $m$-torsion of $E$ is surjective, and that $x\cdot P$ is the identity point precisely when $x=m y$ in $\mathbb{H}[\mathbb{Q},a,b]$ for some $y\in\Lambda$. The conclusion is the conjunction of the two corresponding assertions for $(E',P')$ at every geometric point of $\operatorname{Spec} R'$: every $m$-torsion point there is $x\cdot P'$ for some $x\in\Lambda$, and $x\cdot P'$ is the identity point if and only if $x\in m\Lambda$.
--
--   This is the spreading-out step for full level-$m$ structures on fake elliptic curves: the generation and annihilator conditions at the geometric points over $L$ propagate to all geometric points of the noetherian base $R'$, using that the locus of full generators in the $m$-torsion scheme is clopen and that $\operatorname{Spec}\varphi$ has dense image for injective $\varphi$. It is used in the construction of a finitely generated subalgebra over which the full level-$m$ conditions already hold, in the fine moduli description of the Shimura curve attached to $\mathbb{H}[\mathbb{Q},a,b]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_of_isPullback_of_injective_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.generates_annihilator_of_isPullback_of_injective_of_isUnit
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    (R' L : Type) [CommRing R'] [IsNoetherianRing R'] [CommRing L] (φ : R' →+* L) (hφ : Function.Injective φ)
    (hm : IsUnit ((m : ℕ) : R'))
    (E' : FakeEllipticCurve Λ N R') (P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) E'.f)
    (hP'tor : nsmulPt E'.L (𝟙 (Spec (CommRingCat.of R'))) m P' = E'.L.one (𝟙 (Spec (CommRingCat.of R'))))
    (E : FakeEllipticCurve Λ N L) (gL : E.A ⟶ E'.A)
    (hgL : CategoryTheory.IsPullback gL E.f E'.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gL =
          (E'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, Q.2]⟩).1))
    (hact : ∀ x : ↥Λ, E.act x ≫ gL = gL ≫ E'.act x)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) E.f) (hP : P.1 ≫ gL = Spec.map (CommRingCat.ofHom φ) ≫ P'.1)
    (hgen : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : L →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
          ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = Q)
    (hann : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : L →+* k) (x : ↥Λ),
        pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = E.L.one (geomPoint k sk) ↔
          ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k) (Q : SchemeHomOver (geomPoint k sk) E'.f),
        nsmulPt E'.L (geomPoint k sk) m Q = E'.L.one (geomPoint k sk) →
          ∃ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k sk) = Q) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k) (x : ↥Λ),
        pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k sk) = E'.L.one (geomPoint k sk) ↔
          ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) := by sorry
