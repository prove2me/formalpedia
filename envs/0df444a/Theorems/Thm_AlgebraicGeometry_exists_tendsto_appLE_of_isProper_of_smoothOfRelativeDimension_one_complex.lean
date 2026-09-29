-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex
-- name    : AlgebraicGeometry.exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/fd7114ca-e0b2-5684-9024-fc08eaf2abfe
-- title:
--   Sequential compactness of the ℂ-points of a proper smooth curve
-- statement:
--   Let $Y$ be a scheme and $g : Y \to \operatorname{Spec}\mathbb{C}$ a proper morphism that is smooth of relative dimension $1$, and let $P$ be a sequence, indexed by $\mathbb{N}$, of $\mathbb{C}$-points of $Y$ in the sense of sections of $g$ over the identity: each $P_n$ is a morphism $\operatorname{Spec}\mathbb{C} \to Y$ together with a proof that composing it with $g$ gives $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$. Then there are such a section $Q$ and a strictly monotone $\varphi : \mathbb{N} \to \mathbb{N}$ with the following property: for every affine open $U \subseteq Y$ such that the preimage of $U$ under the underlying morphism of $Q$ is all of $\operatorname{Spec}\mathbb{C}$, there is an $n_0$ such that the same holds for $P_{\varphi(n)}$ for all $n \ge n_0$, and for every $f \in \Gamma(Y, U)$ the sequence of complex numbers obtained by applying $(P_{\varphi(n)})^{\ast}$ on sections from $U$ to the whole of $\operatorname{Spec}\mathbb{C}$ to $f$ and identifying $\Gamma(\operatorname{Spec}\mathbb{C}, \top)$ with $\mathbb{C}$ via `Scheme.ΓSpecIso` — set to $0$ for the finitely many $n < n_0$ — converges, as $n \to \infty$, to the corresponding value of $f$ at $Q$.
--
--   This is the statement that the complex points of a proper smooth curve over $\mathbb{C}$ form a sequentially compact space for the topology in which points are separated by the values of regular functions on affine opens, phrased entirely scheme-theoretically, with no analytification functor. It is used in the complex-analytic steps of the project: in the proof that the locus of points of a fine moduli scheme whose period lattice is a translate of a given quaternionic period lattice is closed, and in the corresponding convergence statement for the abelian-scheme property bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra Filter Topology

theorem AlgebraicGeometry.exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex
    (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper g] (hsm : SmoothOfRelativeDimension 1 g)
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) :
    ∃ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P (φ n)).1 ⁻¹ᵁ U,
          ∀ f : Γ(Y, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P (φ n)).1.appLE U ⊤ (hP n h)) f) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hQ) f))) := by sorry
