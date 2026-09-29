-- Prove2me | Theorems.Thm_Devaney_sarkovskii_of_precedes
-- name    : Devaney.sarkovskii_of_precedes
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T13:05:30.80922+00:00
-- url     : https://prove2.me/theorems/8660bcac-8adb-4bee-beae-d15d6300f142
-- title:
--   Theorem 10.2 (goal) — Sarkovskii's theorem
-- statement:
--   **Goal of the mission.** Let $f : \mathbb{R} \to \mathbb{R}$ be continuous. If $f$ has a periodic point of prime period $k$, and $k \triangleright \ell$ in the Sarkovskii ordering
--
--   $$3 \triangleright 5 \triangleright 7 \triangleright \cdots \triangleright 2\cdot3 \triangleright 2\cdot5 \triangleright \cdots \triangleright 2^2\cdot3 \triangleright \cdots \triangleright 2^3 \triangleright 2^2 \triangleright 2 \triangleright 1,$$
--
--   then $f$ also has a periodic point of prime period $\ell$.
--
--   Continuity is the only hypothesis. Since $3$ heads the ordering, the theorem contains "period three implies all periods" as its first corollary, and since the powers of two come last, it explains why a map with finitely many periodic points can only have dyadic periods.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, p. 62, Theorem 10.2 (Sarkovskii's theorem)

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem sarkovskii_of_precedes (f : ℝ → ℝ) (hf : Continuous f) (k l : ℕ)
    (h : ∃ x, HasPrimePeriod f x k) (hkl : SarkovskiiPrecedes k l) :
    ∃ x, HasPrimePeriod f x l := by sorry
end Devaney
