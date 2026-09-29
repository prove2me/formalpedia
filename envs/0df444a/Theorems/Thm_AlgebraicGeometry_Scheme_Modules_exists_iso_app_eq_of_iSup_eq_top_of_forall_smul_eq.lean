-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
-- name    : AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/701fd778-443c-51a6-9db0-dc58fe775d02
-- title:
--   Modules with frames having matching transition functions are isomorphic
-- statement:
--   Let $X$ be a scheme, let $\iota$ be a linearly ordered type, and let $T : \iota \to$ `X.Opens` be a family of open subsets of $X$ with $\bigsqcup_k T_k = \top$. Let $L$ and $L'$ be objects of `X.Modules`, and let $s_k \in \Gamma(L, T_k)$ and $s'_k \in \Gamma(L', T_k)$ be families of sections such that each $s_k$ is a frame on $T_k$ and each $s'_k$ is a frame on $T_k$, in the sense of `Scheme.Modules.IsFrameOn`: for every open $W \le T_k$ the map $\Gamma(X, W) \to \Gamma(L, W)$, $g \mapsto g \cdot (s_k|_W)$, is bijective, and likewise for $s'_k$ and $L'$. Assume further that for all $i < j$ and every $g \in \Gamma(X, T_i \cap T_j)$, the relation $g \cdot (s_i|_{T_i \cap T_j}) = s_j|_{T_i \cap T_j}$ in $\Gamma(L, T_i \cap T_j)$ implies $g \cdot (s'_i|_{T_i \cap T_j}) = s'_j|_{T_i \cap T_j}$ in $\Gamma(L', T_i \cap T_j)$. Then there exists an isomorphism $e : L \cong L'$ in `X.Modules` whose underlying map on sections over $T_k$ sends $s_k$ to $s'_k$, for every $k$.
--
--   This is the injectivity half of the classification of modules trivialised on a fixed open cover by $\check{H}^1$ of the unit sheaf: two families of frames on the same cover with a common transition cocycle define isomorphic modules, by an isomorphism carrying one family of frames to the other. It is used in the project to produce isomorphisms of invertible modules from local data, for instance in the statements comparing invertibility of a module with invertibility of its pullbacks or of its localisations at primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
    {X : Scheme.{u}} {ι : Type u} [LinearOrder ι] (T : ι → X.Opens) (hT : ⨆ k, T k = ⊤)
    {L L' : X.Modules} (s : ∀ k, Γ(L, T k)) (s' : ∀ k, Γ(L', T k))
    (hs : ∀ k, Scheme.Modules.IsFrameOn (s k) (T k)) (hs' : ∀ k, Scheme.Modules.IsFrameOn (s' k) (T k))
    (h : ∀ (i j : ι), i < j → ∀ g : Γ(X, T i ⊓ T j),
      HSMul.hSMul g (L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i)) =
          L.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s j) →
        HSMul.hSMul g (L'.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s' i)) =
          L'.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s' j)) :
    ∃ e : L ≅ L', ∀ k, e.hom.app (T k) (s k) = s' k := by sorry
