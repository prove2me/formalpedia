-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_basis_smul_pushforward
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_basis_smul_pushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/588159b1-a2e5-557b-bf30-85f86f5432d7
-- title:
--   Basis of π_*𝒪_X times a frame gives basis of π_*L
-- statement:
--   Let $\pi : X \to Y$ be a morphism of schemes, let $L$ be a sheaf of modules on $X$ (an object of `X.Modules`), let $V$ be an open subset of $Y$ and let $d$ be a natural number. Let $e : \mathrm{Fin}\,d \to \Gamma((\text{pushforward }\pi)(\mathbb{1}), V)$ be a family of sections over $V$ of the pushforward along $\pi$ of the monoidal unit $\mathbb{1}_{X.\mathrm{Modules}}$, i.e. of $\pi_*\mathcal{O}_X$, so that each $e\,i$ is also a section of $\mathcal{O}_X$ over $\pi^{-1}V$. Assume: (i) for every open $W \subseteq V$ of $Y$ there is a basis of $\Gamma(\pi_*\mathbb{1}, W)$ over $\Gamma(Y, W)$, indexed by $\mathrm{Fin}\,d$, whose $i$-th member is the restriction of $e\,i$ to $W$; (ii) a section $s \in \Gamma(L, \pi^{-1}V)$ satisfies `IsFrameOn s (π ⁻¹ᵁ V)`, that is, for every open $W$ of $X$ with $W \le \pi^{-1}V$ the map $\Gamma(X, W) \to \Gamma(L, W)$, $g \mapsto g \cdot (s|_W)$, is bijective. The conclusion is that for every open $W \subseteq V$ of $Y$ there is a basis of $\Gamma(\pi_*L, W)$ over $\Gamma(Y, W)$, indexed by $\mathrm{Fin}\,d$, whose $i$-th member is the restriction to $W$ of the section $(e\,i) \cdot s \in \Gamma(\pi_*L, V) = \Gamma(L, \pi^{-1}V)$.
--
--   This is the statement that if $e_1,\dots,e_d$ is a basis of $\pi_*\mathcal{O}_X$ over $V$, compatibly on all smaller opens, and $s$ is a frame of $\mathcal{L}$ on $\pi^{-1}V$, then $e_1 s,\dots,e_d s$ is such a basis of $\pi_*\mathcal{L}$. It is used in the construction of local frames for the norm of an invertible sheaf along a morphism, in [`AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule`](thm.html#AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_basis_smul_pushforward.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_basis_smul_pushforward
    {X Y : Scheme.{u}} (π : X ⟶ Y) {L : X.Modules} {V : Y.Opens} {d : ℕ}
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (he : ∀ (W : Y.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE hW).op (e i))
    {s : Γ(L, π ⁻¹ᵁ V)} (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ V)) :
    ∀ (W : Y.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj L, W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj L).presheaf.map (homOfLE hW).op
          (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s) := by sorry
