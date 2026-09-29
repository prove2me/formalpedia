-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_normal_iff_locally_bounded
-- name    : AhlforsComplexAnalysis.normal_iff_locally_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T05:00:23.881171+00:00
-- url     : https://prove2.me/theorems/f16ae2f8-196e-4b20-be28-0872ace22b8f
-- title:
--   Normal families of analytic functions are the locally bounded ones
-- statement:
--   Let $\Omega$ be a region and $\mathfrak F$ a family of functions analytic in $\Omega$. Then $\mathfrak F$ is normal in $\Omega$ (every sequence in $\mathfrak F$ has a subsequence converging uniformly on every compact subset of $\Omega$) if and only if the functions in $\mathfrak F$ are uniformly bounded on every compact subset of $\Omega$: for each compact $K\subseteq\Omega$ there is $M$ with $|f(z)|\le M$ for all $f\in\mathfrak F$ and $z\in K$.
-- source:
--   L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979 (ISBN 0-07-000657-1), Ch. 5 §5.4, Theorem 15 (p. 224); cited in the proof of Ch. 6 Theorem 1 (p. 231)

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis

theorem AhlforsComplexAnalysis.normal_iff_locally_bounded {Ω : Set ℂ} (hΩ : IsRegion Ω)
    {𝔉 : Set (ℂ → ℂ)} (hanal : ∀ f ∈ 𝔉, AnalyticOnNhd ℂ f Ω) :
    IsNormalFamily 𝔉 Ω ↔
      ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝔉, ∀ z ∈ K, ‖f z‖ ≤ M := by sorry
