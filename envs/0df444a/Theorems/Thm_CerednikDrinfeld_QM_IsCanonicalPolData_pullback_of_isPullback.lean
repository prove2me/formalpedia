-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2197972e-96c3-56e1-b2c8-5ce9a74ed70f
-- title:
--   Canonical polarisation data are stable under base change
-- statement:
--   Let $\varphi\colon S \to S'$ be a homomorphism of commutative rings, let $f\colon A \to \operatorname{Spec} S$ and $f'\colon A' \to \operatorname{Spec} S'$ be morphisms of schemes, and let $L$, $L'$ be relative group laws for $f$, $f'$ (functorial group structures on the sets of $T$-points over the respective bases, with unit, inverse, associativity and naturality under base-change of the test morphism). Let $I$ be an index set, $\mathrm{act}\colon I \to \operatorname{End}(A)$ and $\mathrm{act}'\colon I \to \operatorname{End}(A')$ families of endomorphisms over $f$ respectively $f'$ (i.e. $\mathrm{act}(x)$ followed by $f$ equals $f$, and likewise for $\mathrm{act}'$), and $\mathrm{star}\colon I \to I$ an index map. Assume given $g_A\colon A' \to A$ such that the square formed by $g_A$, $f'$, $f$ and $\operatorname{Spec}\varphi$ is cartesian, such that for every scheme $T$, every $t'\colon T \to \operatorname{Spec} S'$ and all $T$-points $x,y$ of $A'$ over $t'$ the $L'$-product of $x$ and $y$ composed with $g_A$ equals the $L$-product of $x \circ g_A$ and $y \circ g_A$ as $T$-points over $t'$ followed by $\operatorname{Spec}\varphi$, and such that $\mathrm{act}'(x)$ followed by $g_A$ equals $g_A$ followed by $\mathrm{act}(x)$ for every $x \in I$. Let $\mathcal{L}$ be a module on $A$ satisfying `IsCanonicalPolData` for $(f,L,\mathrm{act},\mathrm{star})$, that is: $\mathcal{L}$ is invertible; $\mathcal{L}$ is symmetric, meaning that its pullback along the inversion morphism of $L$ is isomorphic to $\mathcal{L}$ locally over the base; the kernel condition holds, namely a point $x$ over $t$ has the slice of the Mumford bundle of $(f,L,\mathcal{L})$ locally trivial over the base if and only if $x$ is $2$-torsion for $L$; there is a faithfully flat $S$-algebra $S_1$ such that for every relative group law on $A \times_{\operatorname{Spec} S} \operatorname{Spec} S_1$ compatible with $L$ through the first projection, the pullback of $\mathcal{L}$ is, locally over the base, isomorphic to $\mathcal{L}_0 \otimes [-1]^{*}\mathcal{L}_0$ for some invertible $\mathcal{L}_0$ with trivial kernel; for every algebraically closed field $k$ and every $S \to k$ the geometric-fibre $H^0$ rank of $\mathcal{L}$ is positive; and $\mathcal{L}$ is Rosati compatible with $\mathrm{act}$ and $\mathrm{star}$, in the sense that for each $b \in I$ the two pullbacks of the Mumford bundle along $(\mathrm{id},\mathrm{act}(b))$ and along $(\mathrm{act}(\mathrm{star}(b)),\mathrm{id})$ on $A \times_{\operatorname{Spec} S} A$ agree locally over the base. Then the pullback $(g_A)^{*}\mathcal{L}$ satisfies `IsCanonicalPolData` for $(f',L',\mathrm{act}',\mathrm{star})$.
--
--   This is the base-change stability of the package of conditions singling out the canonical polarisation on a fake elliptic curve: all five clauses (invertibility, symmetry, kernel equal to the $2$-torsion, existence of a principal square root after a faithfully flat base change, positivity on geometric fibres, and Rosati compatibility with the quaternionic action) descend along a cartesian square over $\operatorname{Spec}\varphi$. It is used in the construction of quaternionic structures on polarised abelian schemes and in the associated existence statements for pullback families over the moduli problems with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem CerednikDrinfeld.QM.IsCanonicalPolData.pullback_of_isPullback
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act' : I → (A' ⟶ A')) (act_over' : ∀ x : I, act' x ≫ f' = f') (star : I → I)
    (gA : A' ⟶ A) (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ gA =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hact : ∀ x : I, act' x ≫ gA = gA ≫ act x)
    (𝓛 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛) :
    IsCanonicalPolData f' L' act' act_over' star ((Scheme.Modules.pullback gA).obj 𝓛) := by sorry
