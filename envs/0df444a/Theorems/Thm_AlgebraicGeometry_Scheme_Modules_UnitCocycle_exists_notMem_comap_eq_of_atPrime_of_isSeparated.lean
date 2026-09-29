-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated
-- name    : AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_notMem_comap_eq_of_atPrime_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/cd66104e-0b05-5571-8c6a-a584847e2387
-- title:
--   Unit cocycles over S_𝔭 descend to a basic open
-- statement:
--   Let $S$ be a commutative ring, $\mathfrak p$ a prime ideal of $S$, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a quasi-compact separated morphism; let $\iota$ be a finite index type and $W : \iota \to A.\mathrm{Opens}$ a family of opens of $A$, each affine. For a ring $T$ with an $S$-algebra structure write $\mathrm{pr}_T$ for the first projection of the pullback of $f$ along $\operatorname{Spec}$ of $S \to T$. Assume the opens $\mathrm{pr}_{S_{\mathfrak p}}^{-1} W_k$ cover $A \times_{\operatorname{Spec} S} \operatorname{Spec} S_{\mathfrak p}$, and let $g$ be a `UnitCocycle` for this family, that is, sections $g_{ij} \in \Gamma(\mathrm{pr}_{S_{\mathfrak p}}^{-1}W_i \cap \mathrm{pr}_{S_{\mathfrak p}}^{-1}W_j, \mathcal O)$ with $g_{ii} = 1$ and $g_{ij}g_{jk} = g_{ik}$ after restriction to the triple intersections (whence each $g_{ij}$ is a unit). Then there exist $r \in S$ with $r \notin \mathfrak p$, a ring homomorphism $\psi : S_r \to S_{\mathfrak p}$ compatible with the structure maps from $S$, and a `UnitCocycle` $c$ for the family $\mathrm{pr}_{S_r}^{-1}W_k$, such that these opens cover $A \times_{\operatorname{Spec} S} \operatorname{Spec} S_r$ and, writing $\tau$ for the morphism of pullbacks induced by $\mathrm{pr}_{S_{\mathfrak p}}$ and by $\operatorname{Spec} \psi$ on second factors, the pullback $\tau^{*}c$ equals $g$ componentwise: for all $i, j$ and every witness of the (valid) identification of $\mathrm{pr}_{S_{\mathfrak p}}^{-1}W_i \cap \mathrm{pr}_{S_{\mathfrak p}}^{-1}W_j$ with $\tau^{-1}(\mathrm{pr}_{S_r}^{-1}W_i) \cap \tau^{-1}(\mathrm{pr}_{S_r}^{-1}W_j)$, transporting $(\tau^{*}c)_{ij}$ along that identification gives $g_{ij}$.
--
--   This is the spreading-out step for Čech $1$-cocycles with values in $\mathcal O^{\times}$: a cocycle on a finite affine cover of the fibre product over the local ring $S_{\mathfrak p}$ already comes from one over a basic localisation $S_r$, $r \notin \mathfrak p$, the sections over the preimages of affine opens being localisations of the sections over those opens. It is used in the proof that invertibility of a module on the base change to $S_{\mathfrak p}$ propagates to the base change to some basic open neighbourhood of $\mathfrak p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_notMem_comap_eq_of_atPrime_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_notMem_comap_eq_of_atPrime_of_isSeparated
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    [QuasiCompact f] [IsSeparated f] (𝔭 : Ideal S) [𝔭.IsPrime]
    {ι : Type u} [Finite ι] (W : ι → A.Opens) (hW : ∀ k, IsAffineOpen (W k))
    (hcov : (⨆ k, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W k) = ⊤)
    (g : Scheme.Modules.UnitCocycle fun k =>
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W k) :
    ∃ (r : S) (_ : r ∉ 𝔭) (ψ : Localization.Away r →+* Localization.AtPrime 𝔭)
      (hψ : ψ.comp (algebraMap S (Localization.Away r)) = algebraMap S (Localization.AtPrime 𝔭))
      (c : Scheme.Modules.UnitCocycle fun k =>
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W k),
      (⨆ k, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W k) = ⊤ ∧
      ∀ (i j : ι)
        (e : (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W i ⊓
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))) ⁻¹ᵁ W j =
            (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
                  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ
              ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W i) ⊓
            (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
                  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ
              ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))) ⁻¹ᵁ W j)),
        (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭))))).presheaf.map
            (eqToHom e).op
            ((c.comap
              (Limits.pullback.lift
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
                (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
                  Spec.map (CommRingCat.ofHom ψ))
                (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]))).u i j) =
          g.u i j := by sorry
