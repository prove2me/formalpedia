-- Prove2me | Theorems.Thm_EquivMapsEnt_Detect_peter_weyl_truncation
-- name    : EquivMapsEnt.Detect.peter_weyl_truncation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:36.885003+00:00
-- url     : https://prove2.me/theorems/c42dae66-964c-4a69-ac91-8b8c7d80054e
-- title:
--   Equations (24)–(25): finite dimensional invariant exhaustion of the regular action
-- statement:
--   Let $\mu$ be Haar probability measure on $U_n$ and $H=L^2(U_n,\mathbb C^N;\mu)$. The regular action $V(W)\psi(U)=\psi(W^{-1}U)$ admits an increasing sequence of finite dimensional complex subspaces $K_d\subseteq H$ such that every $K_d$ is invariant under every $V(W)$ and
--
--   $$\overline{\bigcup_{d\ge 0}K_d}=H.$$
--
--   This is the consequence of the Peter–Weyl decompositions (24)–(25) used to pass from the infinite dimensional detector to finite matrix detectors. The subspaces are chosen together, before any state is tested.
--
--   **Formalization Note** The source's index $d\ge0$ is a natural number. The source's Haar probability measure is passed as a measure with the corresponding Mathlib typeclass properties.
-- source:
--   Bardet, Collins & Sapra, Characterization of equivariant maps and application to entanglement detection, arXiv:1811.08193v3, p. 14, equations (24)–(25) and the following finite-set exhaustion

import Definitions.Def_EquivMapsEnt_Detect_Lift

namespace EquivMapsEnt.Detect

open MeasureTheory
open scoped Matrix ComplexOrder

/-- The finite-dimensional invariant exhaustion supplied by (24)–(25). -/
theorem peter_weyl_truncation (n N : ℕ)
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ))
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ K : ℕ → Submodule ℂ (LiftSpace n N μ),
      Monotone K ∧
      (∀ d, FiniteDimensional ℂ (K d)) ∧
      (∀ d (W : Matrix.unitaryGroup (Fin n) ℂ)
        (ψ : LiftSpace n N μ), ψ ∈ K d → regRep μ W ψ ∈ K d) ∧
      Dense (⋃ d, (K d : Set (LiftSpace n N μ))) := by sorry

end EquivMapsEnt.Detect
