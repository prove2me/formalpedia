-- Prove2me | Theorems.Thm_Erdos287_inverse_exponential_phase_exact_reduced_period
-- name    : Erdos287.inverse_exponential_phase_exact_reduced_period
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T15:57:02.80147+00:00
-- url     : https://prove2.me/theorems/3dc5aee5-101d-567e-94b9-e0dd761fab24
-- title:
--   Exact reduced period of a modular inverse phase
-- statement:
--   Let $x$ and $y$ be units modulo $m>0$ with inverses $u$ and $v$. Put $g=\gcd(a,m)$ and $q=m/g$. Then $a/g$ is coprime to $q$, and $au\equiv av\pmod m$ holds exactly when $x\equiv y\pmod q$.
-- source:
--   Erdős #287 Type II dispersion audit.

import Mathlib

theorem Erdos287.inverse_exponential_phase_exact_reduced_period (a m x y u v : ℤ) (hm : 0 < m)
    (hx : x * u ≡ 1 [ZMOD m]) (hy : y * v ≡ 1 [ZMOD m]) :
    let g : ℤ := Int.gcd a m
    let q := m / g
    let b := a / g
    Int.gcd b q = 1 ∧ ((a * u ≡ a * v [ZMOD m]) ↔ (x ≡ y [ZMOD q])) := by sorry
