-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_hurwitz
-- name    : AhlforsComplexAnalysis.hurwitz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T04:56:31.783727+00:00
-- url     : https://prove2.me/theorems/697a8f15-409d-4bcc-ae92-96ae640decd4
-- title:
--   Hurwitz's theorem
-- statement:
--   Let $\Omega$ be a region and let $f_n$ ($n=0,1,2,\dots$) be analytic in $\Omega$ with $f_n(z)\neq0$ for all $z\in\Omega$. If $f_n\to f$ uniformly on every compact subset of $\Omega$, then either $f(z)=0$ for all $z\in\Omega$ or $f(z)\neq0$ for all $z\in\Omega$.
-- source:
--   L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979 (ISBN 0-07-000657-1), Ch. 5 §1.1, Theorem 2 (p. 178)

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis

theorem AhlforsComplexAnalysis.hurwitz {Ω : Set ℂ} (hΩ : IsRegion Ω) {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hF : ∀ n, AnalyticOnNhd ℂ (F n) Ω) (hF0 : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hconv : ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn F f Filter.atTop K) :
    (∀ z ∈ Ω, f z = 0) ∨ (∀ z ∈ Ω, f z ≠ 0) := by sorry
