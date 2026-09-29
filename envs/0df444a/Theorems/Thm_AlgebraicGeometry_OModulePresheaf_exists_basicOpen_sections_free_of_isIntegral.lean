-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral
-- name    : AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/ec9d94b2-3278-56af-9f80-b90486f55e26
-- title:
--   Generic freeness on an integral closed subscheme of a proper scheme
-- statement:
--   Let $R$ be a Noetherian commutative ring, $V$ a scheme and $\pi \colon V \to \operatorname{Spec} R$ a proper morphism. Let $Z_0$ be a closed subset of $V$ with $Z_0 \neq \emptyset$, write $i \colon Z \to V$ for the closed immersion of the subscheme cut out by the vanishing ideal sheaf of $Z_0$, and assume that $Z$ is integral. Let $H$ be a presheaf-of-modules datum for the composite $i$ followed by $\pi$: an assignment $U \mapsto H(U)$ of abelian groups to the opens of $Z$, each carrying an $R$-module and a $\Gamma(Z,U)$-module structure that are compatible over the $R$-algebra structure of $\Gamma(Z,U)$ induced by the composite, together with $R$-linear restriction maps compatible with the rings' restrictions, reflexive and transitive. Assume the push-forward $U \mapsto H(i^{-1}U)$, with its $\Gamma(V,U)$-action through $\Gamma(V,U) \to \Gamma(Z, i^{-1}U)$, is coherent, i.e. $H(i^{-1}U)$ is a finite $\Gamma(V,U)$-module for every affine open $U \subseteq V$, and quasi-coherent, i.e. for every affine open $U \subseteq V$ and every $f \in \Gamma(V,U)$ each element of $H(i^{-1}D(f))$ becomes, after multiplication by some power of $f$, the restriction of an element of $H(i^{-1}U)$, and every element of $H(i^{-1}U)$ restricting to $0$ on $i^{-1}D(f)$ is annihilated by some power of $f$. The conclusion is that there exist an affine open $U_0 \subseteq V$ and $f \in \Gamma(V, U_0)$ with $D(f) \cap Z_0 \neq \emptyset$, an integer $r \geq 0$ and sections $y_1, \dots, y_r \in H(i^{-1}U_0)$ such that for every affine open $W \subseteq V$ with $W \leq D(f)$ the map
--   $$\Gamma(Z, i^{-1}W)^r \longrightarrow H(i^{-1}W), \qquad (m_1,\dots,m_r) \longmapsto \sum_{k} m_k \cdot (y_k|_{i^{-1}W}),$$
--   formed with the restriction maps of $H$ along $i^{-1}W \subseteq i^{-1}U_0$, is bijective.
--
--   This is the generic-freeness step for a coherent, quasi-coherent module datum on an integral closed subscheme: over a suitable basic open meeting $Z_0$ the module is free of some rank $r$ with a basis given by globally chosen sections, uniformly over all affine opens inside that basic open. It feeds the finiteness results for the Čech complex of push-forwards along closed immersions, [`AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih) and [`AlgebraicGeometry.OModulePresheaf.forall_pushforward_of_isIntegral`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_pushforward_of_isIntegral), in the proof of finiteness of cohomology for proper morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    {Z₀ : TopologicalSpace.Closeds V} (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent) :
    ∃ (U₀ : V.affineOpens) (f : Γ(V, U₀.1)), ((V.basicOpen f : Set V) ∩ Z₀).Nonempty ∧
      ∃ (r : ℕ) (y : Fin r → H.obj ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ U₀.1)),
        ∀ (W : V.Opens) (hW : W ≤ V.basicOpen f), IsAffineOpen W →
          Function.Bijective (fun m : Fin r →
              Γ((Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme,
                (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ W) =>
            (∑ i, m i • H.res ((TopologicalSpace.Opens.map
                (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base).monotone
                  (hW.trans (V.basicOpen_le f))) (y i) :
              H.obj ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ W))) := by sorry
