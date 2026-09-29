-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact
-- name    : AlgebraicGeometry.IsClosedImmersion.isClosed_iInf_preimage_and_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/3bcced1b-a18e-5823-8ddb-97cd43ce73b1
-- title:
--   Closed immersions preserve closed, quasi-compact-over-the-base finite intersections
-- statement:
--   Let $B$, $E$, $P$ be schemes, let $m : E \to P$ be a morphism which is a closed immersion, and let $\pi_P : P \to B$ be a morphism. Let $\iota$ be a finite index type and $(W_j)_{j \in \iota}$ a family of open subschemes (elements of `P.Opens`) of $P$. Assume that the underlying set of the infimum $\bigwedge_j W_j$ in the frame of opens of $P$ — that is, the intersection $\bigcap_j W_j$ — is a closed subset of $P$, and that the composite of the canonical open immersion $(\bigwedge_j W_j).\iota$ into $P$ with $\pi_P$ is a quasi-compact morphism. The conclusion is the conjunction of two assertions about the open subscheme $\bigwedge_j m^{-1}(W_j)$ of $E$ obtained as the infimum of the scheme-theoretic preimages $m \mathbin{⁻¹ᵁ} W_j$: first, its underlying set is closed in $E$; second, the composite of its canonical open immersion into $E$ with $m$ and then with $\pi_P$ is a quasi-compact morphism. Thus both closedness and quasi-compactness over $B$ of a finite intersection of open pieces are inherited by its preimage under a closed immersion.
--
--   This is a stability statement for the pair of conditions 'closed in the total space' and 'quasi-compact over the base' under pullback along a closed immersion, for finite intersections of open subschemes. It is used in the construction of table schemes, in [`AlgebraicGeometry.exists_tableScheme_of_represents_homScheme`](thm.html#AlgebraicGeometry.exists_tableScheme_of_represents_homScheme).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.IsClosedImmersion.isClosed_iInf_preimage_and_quasiCompact
    {B E P : Scheme.{u}} (m : E ⟶ P) (hm : IsClosedImmersion m) (πP : P ⟶ B)
    {ι : Type v} [Finite ι] (W : ι → P.Opens)
    (hW : IsClosed ((⨅ j, W j : P.Opens) : Set P)) (hW' : QuasiCompact ((⨅ j, W j).ι ≫ πP)) :
    IsClosed ((⨅ j, m ⁻¹ᵁ (W j) : E.Opens) : Set E) ∧
      QuasiCompact ((⨅ j, m ⁻¹ᵁ (W j)).ι ≫ m ≫ πP) := by sorry
