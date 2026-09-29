-- Prove2me | Theorems.Thm_CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app
-- name    : CerednikDrinfeld.eval_app_pullback_fst_eq_algebraMap_eval_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/45b3609c-8f9f-5760-97a7-f6d6275c6438
-- title:
--   Values of pulled-back sections at a base-changed point
-- statement:
--   Let $R \to C$ be a homomorphism of commutative rings (given as an $R$-algebra structure on $C$), let $f : \mathcal X \to S$ be a morphism of schemes and $s_C : \operatorname{Spec} C \to S$ an $S$-valued point, and form the pullback $\mathcal X \times_S \operatorname{Spec} C$ with its two projections. Let $p : \operatorname{Spec} R \to \mathcal X$, and let $q : \operatorname{Spec} C \to \mathcal X \times_S \operatorname{Spec} C$ satisfy the two hypotheses that $q$ followed by the first projection equals $\operatorname{Spec}$ of the structure map $R \to C$ followed by $p$, and that $q$ followed by the second projection is the identity of $\operatorname{Spec} C$. Let $V$ be an open of $\mathcal X$ with $\top \le p^{-1}V$, let $W$ be an open of the pullback with $W \le \mathrm{pr}_1^{-1}V$, and assume $\top \le q^{-1}W$. The conclusion is a conjunction. First, for every section $s \in \mathcal O_{\mathcal X}(V)$: pulling $s$ back along the first projection, restricting to $W$, applying the comorphism of $q$ on $W$, restricting to the top open of $\operatorname{Spec} C$ and reading the result through $\Gamma(\operatorname{Spec} C) \cong C$ gives the image under $R \to C$ of the corresponding element of $R$ obtained from $s$ by the comorphism of $p$ and $\Gamma(\operatorname{Spec} R) \cong R$. Second, for every $c \in C$: viewing $c$ as a global section of $\operatorname{Spec} C$, pulling it back along the second projection, restricting to $W$, applying the comorphism of $q$ and reading the result through $\Gamma(\operatorname{Spec} C) \cong C$ returns $c$.
--
--   This is the standard compatibility of evaluation of sections at a ring-valued point with base change: a $C$-point $q$ of $\mathcal X \times_S \operatorname{Spec} C$ lying over an $R$-point $p$ of $\mathcal X$ evaluates pulled-back sections by applying $R \to C$, and evaluates the second coordinate tautologically. It is used in the construction of the evaluation embedding for a Čerednik–Drinfeld quotient, where sections of a chart are evaluated at base-changed points; it is cited by the results on clearing denominators over a cover and on the ring homomorphism from the function field into the invariant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem CerednikDrinfeld.eval_app_pullback_fst_eq_algebraMap_eval_app
    {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    {𝒳 S : Scheme.{0}} (f : 𝒳 ⟶ S) (sC : Spec (CommRingCat.of C) ⟶ S)
    (p : Spec (CommRingCat.of R) ⟶ 𝒳)
    (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC)
    (hq₁ : q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p)
    (hq₂ : q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)))
    (V : 𝒳.Opens) (hpV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ p ⁻¹ᵁ V)
    (W : (Limits.pullback f sC).Opens) (hWV : W ≤ (Limits.pullback.fst f sC) ⁻¹ᵁ V)
    (hqW : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ W) :
    (∀ s : 𝒳.presheaf.obj (Opposite.op V),
      (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
          (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom
            ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom s)))) =
        algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
          (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hpV).op).hom ((p.app V).hom s)))) ∧
    (∀ c : C,
      (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
          (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom
            ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom
              ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c))))) = c) := by sorry
