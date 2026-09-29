-- Prove2me | Theorems.Thm_BrinSquier_supp_finite_components
-- name    : BrinSquier.supp_finite_components
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:15:43.819305+00:00
-- url     : https://prove2.me/theorems/9af6ff64-617a-42b0-a4b3-300ba61d06e3
-- title:
--   Finitely many breakpoints force finitely many components of the support
-- statement:
--   If $f$ is piecewise linear with finitely many breakpoints, then $\operatorname{supp} f$ — an open subset of $\mathbb{R}$, hence a disjoint union of open intervals — has only **finitely many** connected components.
--
--   $$\#\{\text{connected components of } \operatorname{supp} f\} < \infty.$$
--
--
--   The hypothesis is needed: a homeomorphism whose support is $\bigcup_n \left(\tfrac{1}{n+1}, \tfrac{1}{n}\right)$ has infinitely many components.
--
--   The formal statement asserts only finiteness — **no bound** is exported — and it does not claim the components are bounded: a support may perfectly well be a half-line, or all of $\mathbb{R}$.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 495, first step of the proof of Theorem (3.2): for f, g in PLF(R), supp f union supp g is a finite disjoint union of open intervals.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem supp_finite_components {f : ℝ ≃o ℝ} (hf : IsPLF f) :
    {C : Set ℝ | ∃ x ∈ supp f, C = connectedComponentIn (supp f) x}.Finite := by
  sorry

end BrinSquier
