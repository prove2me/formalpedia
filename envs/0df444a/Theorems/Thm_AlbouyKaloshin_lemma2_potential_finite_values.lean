-- Prove2me | Theorems.Thm_AlbouyKaloshin_lemma2_potential_finite_values
-- name    : AlbouyKaloshin.lemma2_potential_finite_values
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:13:11.439412+00:00
-- url     : https://prove2.me/theorems/a95d2f20-ea77-4429-9d5b-8dc968ec987e
-- title:
--   Lemma 2: the potential takes finitely many values on normalized central configurations
-- statement:
--   Let $n\ge1$ and let $m_1,\dots,m_n\in\mathbb C$ be masses such that no nonempty subset of the bodies has total mass zero. Let $A\subset\mathbb C^{2n}\times\mathbb C^{n(n-1)/2}$ be the set of normalized central configurations, i.e. the complex solutions $(x,y,\delta)$ of system (4). Then the potential $U=\sum_{k<l}m_km_l\delta_{kl}$ takes only finitely many values on $A$:
--   $$
--   \#\,U(A)<\infty .
--   $$
--   This is a Sard-type statement: along any continuum of solutions the potential is constant, and it is used to fix the value of $U=I$ in the proof of Theorem 5.
--
--   **Formalization Note** The standing hypothesis of Section 2 (no subset of bodies has total mass zero) is included as a hypothesis.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 541, Lemma 2 (with the standing mass hypothesis of p. 539)

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem lemma2_potential_finite_values (n : ℕ) [NeZero n] (m : Fin n → ℂ)
    (hm : NoZeroSubMass n m) :
    (potential n m '' NormalizedCC n m).Finite := by sorry

end AlbouyKaloshin
