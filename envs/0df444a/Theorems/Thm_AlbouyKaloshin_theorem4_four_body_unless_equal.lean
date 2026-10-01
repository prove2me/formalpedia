-- Prove2me | Theorems.Thm_AlbouyKaloshin_theorem4_four_body_unless_equal
-- name    : AlbouyKaloshin.theorem4_four_body_unless_equal
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:33:46.653586+00:00
-- url     : https://prove2.me/theorems/1536e049-81ff-4312-84ae-ff42854c589f
-- title:
--   Theorem 4: four bodies, finitely many complex solutions unless the masses are equal
-- statement:
--   Let $m_1,m_2,m_3,m_4>0$ be masses that are not all equal. Then system (4) with $n=4$ has finitely many complex solutions: there are finitely many normalized central configurations of four bodies in the complex domain.
--
--   This improves Theorem 3 by reducing the exceptional mass set to the single ray $m_1=m_2=m_3=m_4$.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 562, Theorem 4

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem theorem4_four_body_unless_equal (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (hne : ¬ (m 0 = m 1 ∧ m 1 = m 2 ∧ m 2 = m 3)) :
    (NormalizedCC 4 (fun k => (m k : ℂ))).Finite := by sorry

end AlbouyKaloshin
