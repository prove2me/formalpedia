-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame
-- name    : AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/f1b484e1-3ed1-5811-921e-bd61c2a2e891
-- title:
--   Spreading out the frame locus to a basic open
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f\colon X \to \operatorname{Spec} R$ a universally closed morphism; let $M$ be a sheaf of modules over the structure sheaf of $X$, let $\iota$ be a type, let $m \colon \iota \to \Gamma(M,\top)$ be a family of global sections of $M$ indexed by $\iota$, and let $\mathfrak p$ be a point of $\operatorname{Spec} R$. Call a point $x$ of $X$ good if there are an index $i$ and an open $U \subseteq X$ with $x \in U$ such that for every open $V \le U$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (m_i)|_V$, obtained by restricting $m_i$ along $V \le \top$ and multiplying, is bijective. The hypothesis is that every point $x$ of $X$ whose image $f(x)$ equals $\mathfrak p$ is good. The conclusion is that there exists $g \in R$ with $g \notin \mathfrak p$ such that every point $x$ of $X$ with $f(x)$ in the basic open $D(g)$ is good.
--
--   This is the spreading-out step for the locus where one of finitely many global sections trivialises a sheaf of modules: the condition is known along the fibre over $\mathfrak p$ and is propagated to the whole preimage of a basic open neighbourhood of $\mathfrak p$, in the spirit of the standard properness arguments of EGA III 4.7.1 / EGA IV 9.6.4. It is used by [`AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (M : X.Modules) {ι : Type*} [Finite ι] (m : ι → Γ(M, ⊤)) (𝔭 : PrimeSpectrum R)
    (hgen : ∀ x : X, f x = 𝔭 → ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V)) := by sorry
