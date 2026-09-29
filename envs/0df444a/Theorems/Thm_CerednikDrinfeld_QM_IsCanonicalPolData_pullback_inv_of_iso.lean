-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_inv_of_iso
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.pullback_inv_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/b6e65c5a-54ce-5907-8952-5455257923dd
-- title:
--   Canonical polarisation data transport along a compatible isomorphism
-- statement:
--   Let $S$ be a commutative ring, let $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S$ be morphisms of schemes, and let $L$, $L'$ be relative group laws for $f$ and $f'$ (functorial group structures on $T$-points over $\operatorname{Spec} S$, natural in $T$). Let $I$ be a type, $\mathrm{act} : I \to \operatorname{End}(A)$ and $\mathrm{act}' : I \to \operatorname{End}(A')$ families of endomorphisms over $\operatorname{Spec} S$ (i.e. $\mathrm{act}(x)$ followed by $f$ is $f$, and likewise for $\mathrm{act}'$ and $f'$), and $\star : I \to I$. Let $e : A \cong A'$ be an isomorphism with $e_{\mathrm{hom}}$ followed by $f'$ equal to $f$, such that $e$ is a homomorphism on points: for every $t : T \to \operatorname{Spec} S$ and all $x, y$ over $t$, the composite of $L.\mathrm{mul}\,t\,x\,y$ with $e_{\mathrm{hom}}$ is $L'.\mathrm{mul}$ applied to the composites of $x$ and $y$ with $e_{\mathrm{hom}}$; and such that $e$ intertwines the actions, $\mathrm{act}(x)$ followed by $e_{\mathrm{hom}}$ equal to $e_{\mathrm{hom}}$ followed by $\mathrm{act}'(x)$ for every $x \in I$. Assume a module $\mathcal{L}$ on $A$ satisfies `IsCanonicalPolData` for $(f, L, \mathrm{act}, \star)$, that is: $\mathcal{L}$ is invertible (locally on $A$ its restriction is isomorphic to the unit module); $\mathcal{L}$ is symmetric, the pullback of $\mathcal{L}$ along the inversion morphism of $L$ being isomorphic to $\mathcal{L}$ after restriction over a neighbourhood of each point of $\operatorname{Spec} S$; the kernel of $\mathcal{L}$ is the $2$-torsion, in the sense that for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ over $t$, the slice at $x$ of the Mumford bundle of $\mathcal{L}$ is trivial locally on the base if and only if $L.\mathrm{mul}\,t\,x\,x = L.\mathrm{one}\,t$; there is a faithfully flat $S$-algebra $S'$ such that, for every relative group law $L_1$ on $A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to \operatorname{Spec} S'$ whose multiplication is compatible with that of $L$ along the first projection, $\mathcal{L}$ admits, locally on the base, a square root, i.e. an invertible module $\mathcal{L}_0$ with trivial kernel for $L_1$ such that $\mathcal{L}_0 \otimes [-1]^*\mathcal{L}_0$ is locally isomorphic over the base to the pullback of $\mathcal{L}$; for every algebraically closed field $k$ and every ring homomorphism $S \to k$ the geometric fibre $H^0$ rank of $\mathcal{L}$ is positive; and $\mathcal{L}$ is Rosati-compatible for $(\mathrm{act}, \star)$, the two pullbacks of the Mumford bundle along $(p_1, \mathrm{act}(b) \circ p_2)$ and $(\mathrm{act}(\star b) \circ p_1, p_2)$ on $A \times_{\operatorname{Spec} S} A$ being isomorphic locally on $\operatorname{Spec} S$ for every $b \in I$. The conclusion is that the pullback of $\mathcal{L}$ along $e^{-1} : A' \to A$ satisfies `IsCanonicalPolData` for $(f', L', \mathrm{act}', \star)$.
--
--   This is the transport of a canonical polarisation datum (invertible, symmetric, kernel equal to the $2$-torsion, a square root after faithfully flat base change, positive on geometric fibres, Rosati-compatible) along an isomorphism of group schemes over the base that also intertwines the prescribed families of endomorphisms. It is used in the comparison of quaternionic-multiplication structures on polarised abelian schemes, in particular when identifying such packages up to isomorphism and when recognising pullback squares for them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_inv_of_iso.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem CerednikDrinfeld.QM.IsCanonicalPolData.pullback_inv_of_iso
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f')
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act' : I → (A' ⟶ A')) (act_over' : ∀ x : I, act' x ≫ f' = f') (star : I → I)
    (e : A ≅ A') (he : e.hom ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ e.hom =
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (hact : ∀ x : I, act x ≫ e.hom = e.hom ≫ act' x)
    (𝓛 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛) :
    IsCanonicalPolData f' L' act' act_over' star ((Scheme.Modules.pullback e.inv).obj 𝓛) := by sorry
