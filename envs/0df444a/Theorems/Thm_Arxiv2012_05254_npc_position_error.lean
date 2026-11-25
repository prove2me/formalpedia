-- Prove2me | Theorems.Thm_Arxiv2012_05254_npc_position_error
-- name    : Arxiv2012_05254.npc_position_error
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T04:32:06.832786+00:00
-- url     : https://prove2.me/theorems/26642a59-1023-41ee-be62-42c1e0700ab6
-- title:
--   Eq. (20): the RMS position error of an NPC is the RMS phase error over $2\pi|u_{ab}|$
-- statement:
--   Let $u\ne0$ be the spacing of a baseline. Let the phase offset $\psi$ of its NPC be a random variable with finite variance, and let $\delta s=\psi/(2\pi|u|)$ be the corresponding perpendicular offset of the NPC (eq. 8). Then
--
--   $$\big[\mathrm{Var}(\delta s)\big]^{1/2}=\frac{\big[\mathrm{Var}(\psi)\big]^{1/2}}{2\pi|u|}.$$
--
--   **Formalization Note** Only the exact first equality of eq. (20) is stated. The second relation, $[\mathrm{Var}(\psi)]^{1/2}\approx(S/N)^{-1}$, is an approximation quoted from the literature for high signal-to-noise ratio. It is not stated.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c030; Section 4.1, eq. (20) (first equality), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem npc_position_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u : Plane) (hu : u ≠ 0) (ψ : Ω → ℝ) (hψ : MemLp ψ 2 P) :
    Real.sqrt (variance (fun ω => perpOffset u (ψ ω)) P) =
      Real.sqrt (variance ψ P) / (2 * Real.pi * ‖u‖) := by sorry

end Arxiv2012_05254
