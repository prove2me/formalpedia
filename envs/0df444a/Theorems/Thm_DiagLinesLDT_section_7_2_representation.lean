-- Prove2me | Theorems.Thm_DiagLinesLDT_section_7_2_representation
-- name    : DiagLinesLDT.section_7_2_representation
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:57:12.191345+00:00
-- url     : https://prove2.me/theorems/b1c20e6a-6b53-42b2-a65f-642ddba4e573
-- title:
--   §7.2 — $U_\ell$ is a Hermitian-unitary representation of $S_\ell$ agreeing with $V$ on point labels
-- statement:
--   Let $q=2^r$. For every axis-parallel line $\ell$:
--
--   1. $U_\ell(v)U_\ell(v')=U_\ell(v+v')$ for all $v,v'\in S_\ell$;
--   2. $U_\ell(v)^\dagger=U_\ell(v)$ for all $v\in S_\ell$;
--   3. $U_\ell(v)U_\ell(v)^\dagger=I$ for all $v\in S_\ell$;
--   4. $U_\ell(tw(u))=V(tw(u))$ for all $u\in\ell$ and $t\in\mathbb F_q$.
--
--   The correction by $\sigma_\ell$ is what restores a representation on vertical lines without changing the point measurements.
--
--   Differences from the source:
--   - encoding: q = 2^r → finite field F with ringChar F = 2; reason: the same fields
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §7.2, paragraph before Proposition 7.2, p.23

import Mathlib
import Definitions.Def_DiagLinesLDT_charTwoStrategy

namespace DiagLinesLDT

/-- `v ↦ U_ℓ(v)` is a representation of `S_ℓ` by Hermitian unitaries that agrees with `V` on every
`𝔽_q w(u)`, `u ∈ ℓ`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §7.2, paragraph before Proposition 7.2, p.23.

**Formalization Note** "`q = 2^r`" is `ringChar F = 2`. The clauses are, in order: the representation
property, Hermitian, unitary, agreement on point labels. -/
theorem section_7_2_representation {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F = 2) (ℓ : AxisLine F 2) :
    (∀ v ∈ lineSpan ℓ, ∀ v' ∈ lineSpan ℓ, Uop ℓ v * Uop ℓ v' = Uop ℓ (v + v')) ∧
      (∀ v ∈ lineSpan ℓ, (Uop ℓ v).conjTranspose = Uop ℓ v) ∧
      (∀ v ∈ lineSpan ℓ, Uop ℓ v * (Uop ℓ v).conjTranspose = 1) ∧
      (∀ u ∈ ℓ.1, ∀ t : F, Uop ℓ (t • w u) = Vop (t • w u)) := by sorry

end DiagLinesLDT
