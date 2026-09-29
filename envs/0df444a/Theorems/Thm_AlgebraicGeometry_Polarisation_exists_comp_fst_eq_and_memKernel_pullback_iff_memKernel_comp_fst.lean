-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_comp_fst_eq_and_memKernel_pullback_iff_memKernel_comp_fst
-- name    : AlgebraicGeometry.Polarisation.exists_comp_fst_eq_and_memKernel_pullback_iff_memKernel_comp_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/30367d9b-c8d0-5e1f-b24c-55d53a3aa079
-- title:
--   Kernel membership: t-points of A versus points of A_K
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism equipped with a relative group law $L$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} S$, natural in $T$), and let $\mathcal{L}$ be a module on $A$ that is invertible, i.e. locally on $A$ isomorphic to the unit module. Let $K$ be a commutative ring, $t : \operatorname{Spec} K \to \operatorname{Spec} S$, write $A_K$ for $A \times_{\operatorname{Spec} S} \operatorname{Spec} K$ with projections $\mathrm{pr}_1$ to $A$ and $\mathrm{pr}_2$ to $\operatorname{Spec} K$, and let $L'$ be a relative group law on $\mathrm{pr}_2 : A_K \to \operatorname{Spec} K$. Assume the compatibility $hL'$: for every scheme $T$, every $t' : T \to \operatorname{Spec} K$ and all sections $P, Q$ of $\mathrm{pr}_2$ over $t'$, the composite of $L'.\mathrm{mul}\,t'\,P\,Q$ with $\mathrm{pr}_1$ equals the $L$-product, over $t'$ followed by $t$, of $P$ followed by $\mathrm{pr}_1$ and of $Q$ followed by $\mathrm{pr}_1$. Let $\iota_K := \operatorname{Spec}$ of the identity map $K \to K$ viewed as the structure map of $K$ over itself. Then two assertions hold. First, every section $y$ of $f$ over $t$ is of the form $Q$ followed by $\mathrm{pr}_1$ for some section $Q$ of $\mathrm{pr}_2$ over $\iota_K$. Second, for every such $Q$, membership of $Q$ in the kernel of $\mathrm{pr}_1^{*}\mathcal{L}$ for $(\mathrm{pr}_2, L')$ at $\iota_K$ is equivalent to membership of $Q$ followed by $\mathrm{pr}_1$ in the kernel of $\mathcal{L}$ for $(f, L)$ at $t$; here membership in the kernel at a section $x$ means that the pullback along the slice morphism determined by $x$ of the Mumford bundle $m^{*}\mathcal{L} \otimes (\mathrm{p}_1^{*}\mathcal{L}^{\vee} \otimes \mathrm{p}_2^{*}\mathcal{L}^{\vee})$ on the relevant self-product is isomorphic to the unit module after restriction over some open neighbourhood of each point of the base spectrum.
--
--   This is the dictionary between points of $A$ over a $K$-valued base morphism $t$ and points of the base change $A_K$ over the identity of $\operatorname{Spec} K$, together with the statement that the two notions of lying in the kernel $K(\mathcal{L})$ of the polarisation attached to $\mathcal{L}$ agree under this dictionary. It is used to transfer hypotheses stated at the level of $t$-points of $A$ to the corresponding statements on $A_K$ in the analysis of theta points with prescribed roots.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_comp_fst_eq_and_memKernel_pullback_iff_memKernel_comp_fst.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_comp_fst_eq_and_memKernel_pullback_iff_memKernel_comp_fst
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {K : Type} [CommRing K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (L' : RelativeGroupLaw K (pullback.snd f t))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst f t =
        (L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    (∀ y : SchemeHomOver t f,
      ∃ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K))) (pullback.snd f t), Q.1 ≫ pullback.fst f t = y.1) ∧
    ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K))) (pullback.snd f t),
      Polarisation.MemKernel (pullback.snd f t) L' ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)
          (Spec.map (CommRingCat.ofHom (algebraMap K K))) Q ↔
        Polarisation.MemKernel f L 𝓛 t
          ⟨Q.1 ≫ pullback.fst f t, by
            rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2, Algebra.algebraMap_self, CommRingCat.ofHom_id,
              Spec.map_id, Category.id_comp]⟩ := by sorry
