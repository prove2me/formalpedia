-- Prove2me | Theorems.Thm_BFVBound_F_odd
-- name    : BFVBound.F_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:41:07.170889+00:00
-- url     : https://prove2.me/theorems/a9a2fb4b-6095-48e7-908b-022846b93938
-- title:
--   The BFV product expectation is odd: $F(-s)=-F(s)$
-- statement:
--   **The BFV product expectation is odd.**
--
--   With $F(s)=\frac{8}{3\pi}\,s\,G(s^{2})$ and $G$ the Gauss hypergeometric series in $s^{2}$, we have
--   $$F(-s)=\frac{8}{3\pi}(-s)\,G\bigl((-s)^{2}\bigr)=-\frac{8}{3\pi}s\,G(s^{2})=-F(s).$$
--   ALMPS25 record exactly this ("$F$ is an odd function because it has the form $F(s)=c\cdot s\cdot G(s^2)$"), and
--   it is why the product-side analysis on the negative range of Pauli correlations only needs the *lower* bound on
--   $G$: the sign of $s$ supplies the sign change.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 Section 4.2 Eq. (17); Parekh-Thompson arXiv:2110.07781 Eq. (3); Brandao-Fernandes-Vallentin arXiv:0910.5765; G = 2F1(1/2,1/2;2;.) is the hypergeometric factor of the rank-three product rounding.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace BFVBound

theorem F_odd (s : ℝ) : F (-s) = -F s := by sorry

end BFVBound
