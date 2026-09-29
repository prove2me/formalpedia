-- Prove2me | Theorems.Thm_AlgebraicGeometry_tendsto_appLE_mapPt_complex
-- name    : AlgebraicGeometry.tendsto_appLE_mapPt_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/cd3dbdfe-eb05-5704-be0b-dfadf39de37f
-- title:
--   Morphisms over ℂ preserve convergence of complex points
-- statement:
--   Let $X$ and $Y$ be schemes (in the bottom universe) equipped with morphisms $f : X \to \operatorname{Spec}\mathbb{C}$ and $g : Y \to \operatorname{Spec}\mathbb{C}$, and let $\varphi : X \to Y$ satisfy $g \circ \varphi = f$. A complex point of $X$ here means an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f`, that is, a morphism $\operatorname{Spec}\mathbb{C} \to X$ whose composite with $f$ is the identity of $\operatorname{Spec}\mathbb{C}$; let $P : \mathbb{N} \to$ (complex points of $X$) be a sequence of such and $Q$ one more. Assume: for every affine open $U \subseteq X$ and every witness that the whole of $\operatorname{Spec}\mathbb{C}$ lies in the preimage of $U$ under $Q$, there are an $n_0$ and a witness that the same holds for $P_n$ for all $n \ge n_0$, such that for every $s \in \Gamma(X,U)$ the sequence whose $n$-th term is, for $n \ge n_0$, the complex number obtained from $(P_n)^{*}s \in \Gamma(\operatorname{Spec}\mathbb{C}, \top)$ via `Scheme.ΓSpecIso` (and $0$ otherwise) tends, along `atTop`, to the corresponding value of $s$ at $Q$. The conclusion is the same assertion on $Y$ for the pushed-forward points `mapPt φ hφ (P n)` and `mapPt φ hφ Q`, i.e. the points $\varphi \circ P_n$ and $\varphi \circ Q$: for every affine open $V \subseteq Y$ through which $\varphi \circ Q$ factors, eventually $\varphi \circ P_n$ factors through $V$ and the values of each $t \in \Gamma(Y,V)$ at $\varphi \circ P_n$ converge to its value at $\varphi \circ Q$.
--
--   This is the statement that a morphism of schemes over $\mathbb{C}$ is continuous for the notion of convergence of complex points defined by convergence of the values of sections on affine opens — the scheme-theoretic form of 'regular maps are continuous in the complex topology'. It is used in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_tendsto_appLE_complex`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_tendsto_appLE_complex), where images of convergent sequences of complex points under morphisms (such as the group law of an abelian scheme) must again be convergent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_tendsto_appLE_mapPt_complex.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology

theorem AlgebraicGeometry.tendsto_appLE_mapPt_complex
    {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)} {g : Y ⟶ Spec (CommRingCat.of ℂ)}
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
    (hP : ∀ (U : X.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U,
          ∀ s : Γ(X, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hx) s)))) :
    ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ (mapPt φ hφ Q).1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (mapPt φ hφ (P n)).1 ⁻¹ᵁ U,
          ∀ s : Γ(Y, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((mapPt φ hφ (P n)).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((mapPt φ hφ Q).1.appLE U ⊤ hx) s))) := by sorry
