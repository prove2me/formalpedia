-- Prove2me | Theorems.Thm_DiazModulus_candidate_quotient_rigid
-- name    : DiazModulus.candidate_quotient_rigid
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:33:59.725015+00:00
-- url     : https://prove2.me/theorems/774fee83-b0f1-4e85-918f-27a27b4b4dbb
-- title:
--   Quotients of candidates with commensurable moduli are rigid
-- statement:
--   **Rigidity of quotients of candidates.**
--
--   Let $u, v, w$ be candidates for Diaz's conjecture with $|u|^{2} = c\,|v|^{2}$ for a rational $c$. If $e^{uw/v}$ is algebraic, then
--
--   $$v \in \mathbb{Q}\,u \quad\text{or}\quad w \in \mathbb{Q}\,v \quad\text{or}\quad w \in \mathbb{Q}\,\bar u .$$
--
--   **Consequence (Sidon property).** Fix an algebraic radius $r$ and let $\Phi_r$ be the set of arguments, modulo $\pi$, of the candidates of modulus $r$. If $\varphi_1 + \varphi_2 = \varphi_3 + \varphi_4 \neq 0$ in $\mathbb{R}/\pi\mathbb{Z}$ with all $\varphi_j \in \Phi_r$, then $\{\varphi_1, \varphi_2\} = \{\varphi_3, \varphi_4\}$. In particular $\Phi_r$ contains no three-term progression.
--
--   This is an unconditional constraint on families of candidates that are algebraically independent: `DiazModulus.log_pair_rigid_of_trdeg_one` shows that two candidates of commensurable moduli not related by $\mathbb{Q}u \cup \mathbb{Q}\bar u$ generate transcendence degree two, where the four exponentials theorem in degree one says nothing. The angular triple, `DiazModulus.candidate_exp_angularTriple_transcendental`, is the case $v = \bar u$, $w = u$. Like every exclusion in this mission it is vacuous if Diaz's conjecture holds.
--
--   **Novelty.** The statement is a short consequence of the six exponentials and Gelfond–Schneider theorems. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 6.10. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: the six exponentials theorem (Lang, Ramachandra) and the Gelfond-Schneider theorem (1934).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_quotient_rigid (u v w : ℂ) (hu : IsCandidate u) (hv : IsCandidate v)
    (hw : IsCandidate w) (c : ℚ) (hc : u * conj u = (c : ℂ) * (v * conj v))
    (hz : IsAlgebraic ℚ (Complex.exp (u * w / v))) :
    (∃ r : ℚ, v = (r : ℂ) * u) ∨ (∃ r : ℚ, w = (r : ℂ) * v) ∨ (∃ r : ℚ, w = (r : ℂ) * conj u) := by sorry

end DiazModulus
