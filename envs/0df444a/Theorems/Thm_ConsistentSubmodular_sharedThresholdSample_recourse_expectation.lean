-- Prove2me | Theorems.Thm_ConsistentSubmodular_sharedThresholdSample_recourse_expectation
-- name    : ConsistentSubmodular.sharedThresholdSample_recourse_expectation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:06.783317+00:00
-- url     : https://prove2.me/theorems/5e15513f-9d02-4c38-aeb1-bc7cd515e9a0
-- title:
--   Expected recourse between two shared-threshold samples equals the type $\ell_1$ distance
-- statement:
--   Let $z:\{0,\dots,d-1\}\times\{0,\dots,n-1\}\to\mathbb R$ and, for each element $e<n$, let $T_e$ be a shared-threshold coupling for the vector $t\mapsto z_{t,e}$ (a finite probability law with active sets, marginals $z_{t,e}$, monotone in $z_{\cdot,e}$). Draw the cells $\omega=(\omega_e)_{e<n}$ independently from the product law $\bigotimes_e T_e$, and for each type $t<d$ let
--   $$S_t(\omega)=\{e<n:\ t\in\mathrm{active}_e(\omega_e)\}.$$
--   Then for all $s,t<d$,
--   $$\mathbb E\Bigl[\,|S_s\,\triangle\,S_t|\,\Bigr]\;=\;\sum_{e<n}\bigl|z_{s,e}-z_{t,e}\bigr| .$$
--
--   Thus the samples $S_t$ are coupled so that the expected number of changed elements (the recourse, i.e. the symmetric difference) between types is exactly the $\ell_1$ distance of the corresponding probability vectors. This is the coupling underlying the passage from fractional paths to randomized, low-recourse set sequences in the deterministic reduction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SamplingCardinality.lean#L34-L54 (`ConsistentSubmodular.sharedThresholdSample_recourse_expectation`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold

open scoped BigOperators
open ConsistentSubmodular
variable {n d : ℕ}

theorem ConsistentSubmodular.sharedThresholdSample_recourse_expectation {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (s t : Fin d) :
    (FiniteLaw.product (fun e => (T e).law)).expect
      (fun ω => (recourse (sharedThresholdSample T ω s) (sharedThresholdSample T ω t) : ℝ)) =
      ∑ e, |z s e - z t e| := by sorry
