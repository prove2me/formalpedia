-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_fact_2_4
-- name    : BourgainUnion.Euclidean.fact_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:50.570199+00:00
-- url     : https://prove2.me/theorems/724da56d-7c13-4003-834a-a37ee315165f
-- title:
--   Fact 2.4 — rigidity of isometric realizations
-- statement:
--   Let $Z\subseteq X$ in a metric space, let $H$ be a finite- or countably-dimensional real Hilbert space, and let $\phi:Z\to H$ be an isometry whose image has closed affine span $H$. For any point $x\in X$ and any isometric realization of $Z\cup\{x\}$ in $\ell_2$, there is an isometric realization $\phi_x:Z\cup\{x\}\to H\oplus_2\mathbb R$ such that
--   $$\phi_x(z)=(\phi(z),0)\quad(z\in Z),\qquad \phi_x(x)=(u,a),\quad a\ge0.$$
--   Here $u\in H$ is unrestricted; it need not lie in $\phi(Z)$. This is the rigidity interface used for the one-point Euclidean energy bound.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: ℓ₂^n ⊕₂ R and tightness → WithLp 2 (H × ℝ) and closure of affineSpan(range φ)=univ; reason: this is the same Hilbert direct sum and the literal closed-affine-span condition
--   - generalization: the setting after the finite-space reduction on p. 5 → an arbitrary metric ambient space; reason: the rigidity assertion uses only the isometric realization of Z∪{x} and its closed affine span; the same distance-preserving affine identification applies in separable Hilbert space
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 6, Fact 2.4

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Fact 2.4: tight means closed affine span, not surjectivity. Finite and infinite H. -/
theorem fact_2_4 {X : Type*} [MetricSpace X]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (Z : Set X) (φ : Z → H) (hφ : Isometry φ)
    (htight : closure (affineSpan ℝ (Set.range φ) : Set H) = Set.univ)
    (x : X) (φ' : (Z ∪ {x} : Set X) → H2) (hφ' : Isometry φ') :
    ∃ F : (Z ∪ {x} : Set X) → WithLp 2 (H × ℝ), Isometry F ∧
      (∀ z : Z, F ⟨z, Or.inl z.property⟩ = WithLp.toLp 2 (φ z, (0 : ℝ))) ∧
      ∃ u : H, ∃ a : ℝ, 0 ≤ a ∧
        F ⟨x, Or.inr (Set.mem_singleton x)⟩ = WithLp.toLp 2 (u,a) := by sorry

end BourgainUnion.Euclidean
