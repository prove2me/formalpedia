-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/6c3c04a0-3e1e-5c85-90bf-0c622a0fead4
-- title:
--   Tilde criterion via localisation on basic opens
-- statement:
--   Let $R$ be a commutative ring and let $M$ be a sheaf of modules over the structure sheaf of the scheme $X=\operatorname{Spec} R$, i.e. an object of $X$`.Modules`. Assume that for every global section $g \in \Gamma(X,\mathcal O_X)$ the restriction map from global sections of $M$ to sections of $M$ over the basic open $X$`.basicOpen` $g$ satisfies two clauses: first, for every section $x$ of $M$ over that basic open there exist $n \in \mathbb N$ and a global section $y$ of $M$ whose restriction equals $(g^n|_{D(g)}) \cdot x$, the scalar being the restriction of $g^n$ to the basic open acting on $x$; second, every global section $y$ of $M$ whose restriction to that basic open vanishes is killed by some power $g^n$, the action being that of the global sections of $\mathcal O_X$ on the global sections of $M$. Under these hypotheses the canonical morphism `M.fromTildeΓ`, from the sheaf of modules associated with the $R$-module of global sections of $M$ to $M$, is an isomorphism.
--
--   This is the standard criterion identifying a sheaf of $\mathcal O$-modules on an affine scheme with the tilde of its global sections (hence its quasi-coherence) from the condition that sections over each basic open $D(g)$ are the localisation at $g$ of the global sections. It is used in the project to deduce the same conclusion for sheaves of modules that are locally trivial, through [`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.lean

import Mathlib.AlgebraicGeometry.Modules.Tilde

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (hloc : ∀ g : Γ(Spec (.of R), ⊤),
      (∀ x : Γ(M, (Spec (.of R)).basicOpen g), ∃ (n : ℕ) (y : Γ(M, ⊤)),
          M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y
            = ((Spec (.of R)).presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op).hom (g ^ n) • x)
        ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n) • y = 0)) :
    IsIso M.fromTildeΓ := by sorry
