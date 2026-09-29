-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_of_forall_away_of_locIsoOnBase
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.exists_of_forall_away_of_locIsoOnBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/fed7036d-a383-5317-9962-a115617ebead
-- title:
--   Zariski gluing of canonical polarisation data over the base
-- statement:
--   Let $S$ be a commutative ring, $f : A \to \operatorname{Spec} S$ a morphism of schemes equipped with a relative group law $L$ (a functorial multiplication, unit and inversion on $T$-points over $\operatorname{Spec} S$, satisfying the group axioms and compatible with base change), a family $\mathrm{act} : I \to \operatorname{End}(A)$ of endomorphisms over $\operatorname{Spec} S$ and a map $\star : I \to I$. Assume that for every $r \in S$ the ring map on global sections induced by the projection $A \times_S \operatorname{Spec} S[1/r] \to \operatorname{Spec} S[1/r]$ is surjective. Let $r_1,\dots,r_k \in S$ generate the unit ideal; for each $i$ let $f'_i : A'_i \to \operatorname{Spec} S[1/r_i]$ together with $g_i : A'_i \to A$ form a cartesian square over $S \to S[1/r_i]$, let $L'_i$ be a relative group law on $f'_i$ whose multiplication is carried to that of $L$ by $g_i$, and let $\mathrm{act}'_i : I \to \operatorname{End}(A'_i)$ be endomorphisms over $f'_i$ with $\mathrm{act}'_i(x) \circ$-then-$g_i = g_i$-then-$\mathrm{act}(x)$. Let $\mathcal L'_i$ be modules on $A'_i$ each satisfying `IsCanonicalPolData` for $(f'_i, L'_i, \mathrm{act}'_i, \star)$, i.e.\ invertible, symmetric under the inversion morphism, with kernel of the associated Mumford bundle exactly the $2$-torsion points, locally on the base of the form $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ with $\mathcal L_0$ invertible of trivial kernel after a faithfully flat base change compatible with the group law, with positive $H^0$ on geometric fibres, and Rosati-compatible with respect to $\mathrm{act}'_i$ and $\star$. Assume the agreement condition: for all $i,j$ and every $A_{ij} \to \operatorname{Spec} S[1/(r_ir_j)]$ presented as a base change of $A'_i$ along $S[1/r_i] \to S[1/(r_ir_j)]$ via $p_i$ and of $A'_j$ along $S[1/r_j] \to S[1/(r_ir_j)]$ via $p_j$, with $p_i$-then-$g_i = p_j$-then-$g_j$, the modules $p_i^*\mathcal L'_i$ and $p_j^*\mathcal L'_j$ are isomorphic locally on the base (each point of the base has an open neighbourhood $U$ over whose preimage the two are isomorphic). Then there exists a module $\mathcal L$ on $A$ satisfying `IsCanonicalPolData` for $(f, L, \mathrm{act}, \star)$ such that for every $i$ the pullback $g_i^*\mathcal L$ is isomorphic to $\mathcal L'_i$ locally on the base of $f'_i$.
--
--   This is the descent step which assembles canonical polarisation data on a group scheme over $\operatorname{Spec} S$ from data given over the members of a cover of the base by basic open affines, agreeing on pairwise overlaps only up to isomorphism locally on the base. It is used in the construction of quaternionic structures on polarised abelian schemes, where the polarisation must be produced globally over the base from its local descriptions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_of_forall_away_of_locIsoOnBase.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem CerednikDrinfeld.QM.IsCanonicalPolData.exists_of_forall_away_of_locIsoOnBase
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
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

    (𝓛' : ∀ i, (A' i).Modules)
    (h𝓛' : ∀ i, CerednikDrinfeld.QM.IsCanonicalPolData (f' i) (L' i) (act' i) (act_over' i) star (𝓛' i))

    (hagree : ∀ (i j : Fin k) (Aij : Scheme.{u})
      (fij : Aij ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j))))
      (pi : Aij ⟶ A' i) (pj : Aij ⟶ A' j),
      IsPullback pi fij (f' i)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight (r i) (r j) :
          Localization.Away (r i) →+* Localization.Away (r i * r j)))) →
      IsPullback pj fij (f' j)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft (r j) (r i) :
          Localization.Away (r j) →+* Localization.Away (r i * r j)))) →
      pi ≫ g i = pj ≫ g j →
      LocIsoOnBase fij ((Scheme.Modules.pullback pi).obj (𝓛' i)) ((Scheme.Modules.pullback pj).obj (𝓛' j))) :
    ∃ 𝓛 : A.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f L act act_over star 𝓛 ∧
      ∀ i, LocIsoOnBase (f' i) ((Scheme.Modules.pullback (g i)).obj 𝓛) (𝓛' i) := by sorry
