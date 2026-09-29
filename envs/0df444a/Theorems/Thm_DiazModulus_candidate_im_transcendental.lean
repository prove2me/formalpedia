-- Prove2me | Theorems.Thm_DiazModulus_candidate_im_transcendental
-- name    : DiazModulus.candidate_im_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-12T12:49:11.679873+00:00
-- url     : https://prove2.me/theorems/1e000329-7c05-4c26-8e94-d72745da813c
-- title:
--   The imaginary part of a Diaz candidate is transcendental
-- statement:
--   Let $u\in\mathbb{C}$ be a **candidate** for Diaz's modulus conjecture: $u\neq 0$, $|u|$ algebraic over $\mathbb{Q}$, and $e^{u}$ algebraic over $\mathbb{Q}$. Assume Hermite--Lindemann. Write $u=x+iy$ with $x,y\in\mathbb{R}$. Then
--
--   $$
--   y \text{ is transcendental over }\mathbb{Q}.
--   $$
--
--   If $y$ were algebraic then $x^{2}=|u|^{2}-y^{2}$ would be algebraic, hence so would $x$, hence so would $u=x+iy$, contradicting Hermite--Lindemann.
--
--   **Formalization Note.** Symmetric to `DiazModulus.candidate_re_transcendental`. The hypothesis `HermiteLindemann` is the mission's explicit `Prop`.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 6: stated without a number in the discussion after Proposition 6.14, and listed in Appendix A. Background: G. Diaz, Utilisation de la conjugaison complexe dans l'etude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Theor. Nombres Bordeaux 16 (2004), 535-553, section 5.1. Transcendence of the imaginary coordinate of a hypothetical counterexample.

import Definitions.Def_DiazModulus
open Complex

namespace DiazModulus
theorem candidate_im_transcendental (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    Transcendental ℚ ((u.im : ℝ) : ℂ) := by sorry
end DiazModulus
