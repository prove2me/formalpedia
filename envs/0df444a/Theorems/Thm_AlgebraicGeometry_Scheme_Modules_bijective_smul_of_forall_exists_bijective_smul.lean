-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
-- name    : AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/41f318ac-6959-53a6-a947-4c69807dccda
-- title:
--   Being a generator of a module sheaf is local
-- statement:
--   Let $X$ be a scheme, let $M$ be a sheaf of $\mathcal O_X$-modules on $X$, let $\sigma \in \Gamma(M,\top)$ be a global section of $M$, and let $V$ be an open subset of $X$. For an open $W \subseteq X$ write $\sigma|_W \in \Gamma(M,W)$ for the image of $\sigma$ under the restriction map of the presheaf of $M$ along the inclusion $W \leq \top$, and consider the $\mathcal O_X$-action map $\Gamma(X,W) \to \Gamma(M,W)$, $g \mapsto g \cdot \sigma|_W$. The hypothesis is that every point $x \in V$ admits an open neighbourhood $U$ of $x$ such that for every open $W \leq U$ the map $g \mapsto g \cdot \sigma|_W$ is bijective; note that the opens $U$ are not required to be contained in $V$. The conclusion is that the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma|_V$, is bijective. Thus the property of $\sigma$ that multiplication by $\sigma$ identifies the structure sheaf with $M$ on all sufficiently small opens propagates from a neighbourhood of each point of $V$ to $V$ itself.
--
--   This is the locality statement for a global section being a frame (a free generator) of a module sheaf: the set of opens over which $\sigma$ trivialises $M$ is determined pointwise. It is used in the treatment of invertible module sheaves on schemes, for instance in producing trivialising covers from pointwise or fibrewise generation data, and in the construction of reframings of framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul
    {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W))) :
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : Γ(M, V)) := by sorry
