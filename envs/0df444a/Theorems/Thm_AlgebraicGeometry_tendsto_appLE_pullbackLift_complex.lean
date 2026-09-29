-- Prove2me | Theorems.Thm_AlgebraicGeometry_tendsto_appLE_pullbackLift_complex
-- name    : AlgebraicGeometry.tendsto_appLE_pullbackLift_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/1e503f6b-ea40-586e-8b55-e5f07db1280c
-- title:
--   Convergence of ℂ-points passes to the fibre product
-- statement:
--   Let $X$ and $Y$ be schemes (in universe $0$) together with morphisms $f : X \to \operatorname{Spec}\mathbb{C}$ and $g : Y \to \operatorname{Spec}\mathbb{C}$. A `SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f` is a pair consisting of a morphism $\varphi : \operatorname{Spec}\mathbb{C} \to X$ together with a proof that $\varphi$ followed by $f$ is the identity of $\operatorname{Spec}\mathbb{C}$, i.e. a $\mathbb{C}$-point of $X$ over $\mathbb{C}$; likewise for $g$. Given a sequence $P : \mathbb{N} \to$ such points of $X$ and a point $Q$, the hypothesis `hP` says: for every affine open $U \subseteq X$ with $\top \le Q^{-1}U$ (that is, $Q$ factors through $U$) there are an index $n_0$ and a proof that $\top \le (P_n)^{-1}U$ for all $n \ge n_0$, such that for every section $s \in \Gamma(X, U)$ the sequence whose $n$-th term is the value $s(P_n) \in \mathbb{C}$ for $n \ge n_0$ (obtained from `appLE U ⊤` and the isomorphism $\Gamma(\operatorname{Spec}\mathbb{C},\top) \cong \mathbb{C}$) and $0$ otherwise converges, as $n \to \infty$, to $s(Q)$. The corresponding hypothesis `hP'` is imposed on a sequence $P'$ and a point $Q'$ of $Y$. The conclusion asserts the same convergence property for the paired points of $\operatorname{pullback} f g$ obtained by `pullback.lift` from $(P_n, P'_n)$ and from $(Q, Q')$, regarded as points over $\operatorname{Spec}\mathbb{C}$ via $\operatorname{pullback.fst} f g$ followed by $f$: for every affine open $U$ of the fibre product through which the paired limit point factors, there are $n_0$ and a proof that the paired points $(P_n, P'_n)$ factor through $U$ for $n \ge n_0$, and for every $s \in \Gamma(\operatorname{pullback} f g, U)$ the values $s(P_n, P'_n)$ tend to $s(Q, Q')$.
--
--   This is one direction of the statement that, on $\mathbb{C}$-points, the topology defined by convergence of values of sections on $X \times_{\mathbb{C}} Y$ refines the product topology: pairing two convergent sequences of $\mathbb{C}$-points gives a convergent sequence in the fibre product. It is used in the treatment of abelian schemes, where convergence has to be transported through maps such as the group law $A \times A \to A$, and is cited by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_tendsto_appLE_complex`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_tendsto_appLE_complex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_tendsto_appLE_pullbackLift_complex.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology

theorem AlgebraicGeometry.tendsto_appLE_pullbackLift_complex
    {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)} {g : Y ⟶ Spec (CommRingCat.of ℂ)}
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
    (hP : ∀ (U : X.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U,
          ∀ s : Γ(X, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hx) s))))
    (P' : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (Q' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g)
    (hP' : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q'.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P' n).1 ⁻¹ᵁ U,
          ∀ s : Γ(Y, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P' n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q'.1.appLE U ⊤ hx) s)))) :
    ∀ (U : (pullback f g).Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ (⟨pullback.lift Q.1 Q'.1 (Q.2.trans Q'.2.symm), by rw [pullback.lift_fst_assoc]; exact Q.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (⟨pullback.lift (P n).1 (P' n).1 ((P n).2.trans (P' n).2.symm), by rw [pullback.lift_fst_assoc]; exact (P n).2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1 ⁻¹ᵁ U,
          ∀ s : Γ((pullback f g), U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((⟨pullback.lift (P n).1 (P' n).1 ((P n).2.trans (P' n).2.symm), by rw [pullback.lift_fst_assoc]; exact (P n).2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((⟨pullback.lift Q.1 Q'.1 (Q.2.trans Q'.2.symm), by rw [pullback.lift_fst_assoc]; exact Q.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1.appLE U ⊤ hx) s))) := by sorry
