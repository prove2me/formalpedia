-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_forall_away
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.of_forall_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/c01efc47-172e-5b00-9e11-49dbb2edd1c9
-- title:
--   Canonical polarisation data descend along a basic open cover
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism and $L$ a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over each $t : T \to \operatorname{Spec} S$, natural in $T$. Let $I$ be a type, $\mathrm{act} : I \to \operatorname{End}(A)$ a family of endomorphisms over $\operatorname{Spec} S$ (each $\mathrm{act}\,x$ followed by $f$ equals $f$), and $\mathrm{star} : I \to I$ an arbitrary map. Let $r : \mathrm{Fin}\,k \to S$ generate the unit ideal, and for each $i$ let $f' i : A'_i \to \operatorname{Spec} S[1/r_i]$, together with $g_i : A'_i \to A$ making the square with $f$ and $\operatorname{Spec}$ of $S \to S[1/r_i]$ cartesian, let $L'_i$ be a relative group law for $f' i$ whose multiplication is carried to that of $L$ by $g_i$, and let $\mathrm{act}' i : I \to \operatorname{End}(A'_i)$ consist of endomorphisms over $f' i$ with $\mathrm{act}'\,i\,x$ followed by $g_i$ equal to $g_i$ followed by $\mathrm{act}\,x$. Let $\mathcal L$ be a module on $A$ that is invertible (locally isomorphic to the unit sheaf) and assume each pullback $g_i^*\mathcal L$ is a canonical polarisation datum for $(f' i, L'_i, \mathrm{act}' i, \mathrm{star})$. Then $\mathcal L$ is a canonical polarisation datum for $(f, L, \mathrm{act}, \mathrm{star})$: it is invertible; it is symmetric, i.e. the pullback of $\mathcal L$ under the inversion morphism of $L$ is isomorphic to $\mathcal L$ over the preimages of a neighbourhood of each point of $\operatorname{Spec} S$; its kernel is two-torsion, i.e. for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ of $f$ over $t$, the slice of the Mumford bundle at $x$ is locally trivial over the base exactly when $x +_L x$ is the unit; there exists a faithfully flat $S$-algebra $S'$ such that for every relative group law $L'$ on the base change of $f$ to $S'$ compatible with $L$ there is an invertible $\mathcal L_0$ with trivial kernel whose 'difference' $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ is locally isomorphic over the base to the pullback of $\mathcal L$; for every algebraically closed field $K$ and every ring map $S \to K$ the geometric fibre $H^0$ rank of $\mathcal L$ is positive; and the Rosati compatibility for $\mathrm{act}$ and $\mathrm{star}$ holds, namely the two pullbacks of the Mumford bundle along the two twists of the diagonal pairing by $\mathrm{act}\,b$ and $\mathrm{act}(\mathrm{star}\,b)$ agree locally over the base.
--
--   This is the statement that being a canonical polarisation datum is local on the base for a cover of $\operatorname{Spec} S$ by the basic open sets $D(r_i)$: the datum may be checked after localising away from each $r_i$, the invertibility of $\mathcal L$ being assumed globally. It supports the construction of canonical polarisations on the abelian schemes occurring in the quaternionic moduli problems, and is used by [`CerednikDrinfeld.QM.IsCanonicalPolData.exists_of_forall_away_of_locIsoOnBase`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.exists_of_forall_away_of_locIsoOnBase).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_forall_away.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem CerednikDrinfeld.QM.IsCanonicalPolData.of_forall_away
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (L' : ∀ i, RelativeGroupLaw (Localization.Away (r i)) (f' i))
    (hL' : ∀ (i : Fin k) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
      (x y : SchemeHomOver t' (f' i)),
      ((L' i).mul t' x y).1 ≫ g i =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))
          ⟨x.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, y.2]⟩).1)
    (act' : ∀ i, I → (A' i ⟶ A' i)) (act_over' : ∀ (i : Fin k) (x : I), act' i x ≫ f' i = f' i)
    (hact' : ∀ (i : Fin k) (x : I), act' i x ≫ g i = g i ≫ act x)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hloc : ∀ i, CerednikDrinfeld.QM.IsCanonicalPolData (f' i) (L' i) (act' i) (act_over' i) star
      ((Scheme.Modules.pullback (g i)).obj 𝓛)) :
    CerednikDrinfeld.QM.IsCanonicalPolData f L act act_over star 𝓛 := by sorry
