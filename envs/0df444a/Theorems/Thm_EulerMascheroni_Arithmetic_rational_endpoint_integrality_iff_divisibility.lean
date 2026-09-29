-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_rational_endpoint_integrality_iff_divisibility
-- name    : EulerMascheroni.Arithmetic.rational_endpoint_integrality_iff_divisibility
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:53:02.606775+00:00
-- url     : https://prove2.me/theorems/4e1a90d0-030c-4654-b34f-f14dadde8e7d
-- title:
--   Exact divisibility criterion for rational factorial-quotient endpoints
-- statement:
--   Write $S_m=\sum_{k<m}(-1)^k k!$ and $q_m(a)=(a-S_m)/m!$. For integers $A,B$ with $B\ne0$ and natural $D,m$,
--   $$Dq_m(A/B)\text{ is integral over }\mathbb Z\quad\Longleftrightarrow\quad Bm!\mid D(A-BS_m).$$
--   No coprimality or positivity normalization of $A,B$ is required. This makes the rational case of the missing Gompertz denominator estimate an exact divisibility problem.
-- source:
--   Elementary denominator clearing and integral closedness of the integers; application to the Euler factorial quotient in Matala-aho–Zudilin, https://arxiv.org/html/1703.02633, Section 2.

import Definitions.Def_eulerMascheroni_factorialQuotient
open EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.rational_endpoint_integrality_iff_divisibility (A B : ℤ) (hB : B ≠ 0) (D m : ℕ) :
    IsIntegral ℤ ((D:ℝ)*quotientCoeff ((A:ℝ)/(B:ℝ)) m) ↔
      B*(m.factorial:ℤ) ∣ (D:ℤ)*(A-B*∑ k ∈ Finset.range m, (-1:ℤ)^k*k.factorial) := by sorry
