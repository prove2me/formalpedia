-- Prove2me | Theorems.Thm_DiazModulus_candidate_neg_one_pow_ratio
-- name    : DiazModulus.candidate_neg_one_pow_ratio
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:34:06.398684+00:00
-- url     : https://prove2.me/theorems/db5b6826-5020-4da5-adab-4cfe6bcb5c5d
-- title:
--   For every candidate u, (−1)^{u/ū} = e^{iπu/ū} is transcendental
-- statement:
--   **$(-1)^{u/\bar u}$.**
--
--   For every candidate $u$ of Diaz's conjecture,
--
--   $$(-1)^{u/\bar u} := e^{i\pi u/\bar u} \ \text{is transcendental.}$$
--
--   The exponent $u/\bar u$ has modulus one and is transcendental, so Gelfond–Schneider does not apply; neither of the two theorems used suffices alone. `DiazModulus.conj_ratio_multiplier_relation`, a consequence of six exponentials, shows that algebraicity of $e^{i\pi u/\bar u}$ would force $\pi\operatorname{Im}u \in \mathbb{Q}\,|u|^{2}$. That makes $u$ algebraic over $\mathbb{Q}(\pi)$, and then the four exponentials theorem in transcendence degree one closes the case. Like every exclusion in this mission it is vacuous if Diaz's conjecture holds.
--
--   **Novelty.** The statement is a short consequence of the six exponentials theorem and the four exponentials theorem in transcendence degree one. For candidates with $1$, $\pi u$, $\pi\bar u$ linearly independent over $\overline{\mathbb{Q}}$, among them every candidate algebraically independent of $\pi$, it also follows from Corollaire 4(4) of G. Diaz (J. Théor. Nombres Bordeaux 19, 2007, p. 383) at $(\lambda_1, \lambda_3) = (u, -i\pi)$, a consequence of Roy's strong six exponentials theorem. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 6, after Corollary 6.11. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: the six exponentials theorem (Lang, Ramachandra) and the four exponentials theorem in transcendence degree one (Brownawell 1974; Waldschmidt 1973).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_neg_one_pow_ratio (u : ℂ) (hu : IsCandidate u) :
    Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I * u / conj u)) := by sorry

end DiazModulus
