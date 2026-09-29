-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
-- name    : AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/436c686f-980d-5847-a5d6-b0e5f9e9f475
-- title:
--   Gluing frame pairs to an isomorphism of modules
-- statement:
--   Let $X$ be a scheme and let $P$, $Q$ be $\mathcal{O}_X$-modules (objects of `X.Modules`). Suppose given, for each open $W \subseteq X$, a set $S(W)$ of pairs $(p,q)$ with $p \in \Gamma(P,W)$ and $q \in \Gamma(Q,W)$, subject to four hypotheses. First, `hframe`: for every open $W$ and every pair $(p,q) \in S(W)$, both $p$ and $q$ satisfy `IsFrameOn` on $W$, that is, for every open $W' \leq W$ the map $\Gamma(X,W') \to \Gamma(P,W')$, $g \mapsto g \cdot (p|_{W'})$, and likewise the map $g \mapsto g \cdot (q|_{W'})$ into $\Gamma(Q,W')$, are bijective. Second, `hcov`: every point $x \in X$ lies in some open $W$ with $S(W)$ nonempty. Third, `hres`: if $W' \leq W$ and $(p,q) \in S(W)$, then the pair of restrictions $(p|_{W'}, q|_{W'})$ lies in $S(W')$. Fourth, `hunit`: any two pairs $(p,q)$, $(p',q')$ in the same $S(W)$ differ by a single section, i.e. there is $u \in \Gamma(X,W)$ with $p' = u \cdot p$ and $q' = u \cdot q$. The conclusion is the existence of an isomorphism $e : P \cong Q$ of $\mathcal{O}_X$-modules such that for every open $W$ and every $(p,q) \in S(W)$ one has $e_{W}(p) = q$, where $e_W$ denotes the component of the forward map of $e$ at $W$.
--
--   This is a torsor-style gluing principle: a system of local pairs of frames of $P$ and $Q$, covering $X$, stable under restriction and pairwise proportional by a common section, determines a global isomorphism $P \cong Q$ matching the distinguished frames. It underlies the construction of canonical isomorphisms between modules presented by local frames, and is invoked in the gluing of cocycle data and in the multiplicativity statements for norms of line bundles along finite locally free morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul
    {X : Scheme.{u}} {P Q : X.Modules} (S : ∀ W : X.Opens, Set (Γ(P, W) × Γ(Q, W)))
    (hframe : ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      Scheme.Modules.IsFrameOn pq.1 W ∧ Scheme.Modules.IsFrameOn pq.2 W)
    (hcov : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty)
    (hres : ∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      (P.presheaf.map (homOfLE h).op pq.1, Q.presheaf.map (homOfLE h).op pq.2) ∈ S W')
    (hunit : ∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)), pq ∈ S W → pq' ∈ S W →
      ∃ u : Γ(X, W), pq'.1 = u • pq.1 ∧ pq'.2 = u • pq.2) :
    ∃ e : P ≅ Q, ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W → e.hom.app W pq.1 = pq.2 := by sorry
