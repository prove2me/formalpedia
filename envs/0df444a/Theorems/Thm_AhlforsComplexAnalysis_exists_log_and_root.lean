-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_exists_log_and_root
-- name    : AhlforsComplexAnalysis.exists_log_and_root
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T04:45:47.369214+00:00
-- url     : https://prove2.me/theorems/3ad33487-b851-4a36-aa40-deef38e6f753
-- title:
--   Logarithms and $n$-th roots on simply connected regions
-- statement:
--   Let $\Omega$ be a simply connected region (complement in the extended plane connected) and let $f$ be analytic in $\Omega$ with $f(z)\neq 0$ for all $z\in\Omega$. Then:
--
--   1. there is an analytic function $L$ in $\Omega$ with $e^{L(z)}=f(z)$ for all $z\in\Omega$ (a single-valued branch of $\log f$), and
--   2. for every integer $n\ge 1$ there is an analytic function $R$ in $\Omega$ with $R(z)^n=f(z)$ for all $z\in\Omega$ (a single-valued branch of $\sqrt[n]{f}$).
-- source:
--   L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979 (ISBN 0-07-000657-1), Ch. 4 §4.4, Corollary 2 of Theorem 15 (p. 142)

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis

theorem AhlforsComplexAnalysis.exists_log_and_root {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    (∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L Ω ∧ ∀ z ∈ Ω, Complex.exp (L z) = f z) ∧
    ∀ n : ℕ, 0 < n → ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R Ω ∧ ∀ z ∈ Ω, R z ^ n = f z := by sorry
