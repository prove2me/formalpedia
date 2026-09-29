-- Prove2me | Theorems.Thm_Diaz_candidate_no_vanishing_coeff_Qbar
-- name    : Diaz.candidate_no_vanishing_coeff_Qbar
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:30.733917+00:00
-- url     : https://prove2.me/theorems/16400e12-6f0a-4e53-b7b6-bcf77ad662da
-- title:
--   A candidate's rank-one matrix has no vanishing coefficient over $\bar{\mathbb{Q}}$
-- statement:
--   Let $u \in \mathbb{C}$ be a **candidate** for Diaz's modulus conjecture: $u \neq 0$ and $e^{u}$ algebraic over $\mathbb{Q}$. Suppose $r \in \bar{\mathbb{Q}}$ with $u\bar u = r^{2}$, so $r$ is an algebraic square root of $|u|^{2}$. Let $w, v \in \mathbb{C}^{2}$ be non-zero with all entries algebraic. Then
--
--   $$\sum_{i}\sum_{j} w_i \, H(u,r)_{ij}\, v_j \ \neq\ 0, \qquad H(u,r) = \begin{pmatrix} u & r \\ r & \bar u \end{pmatrix}.$$
--
--   **Why.** Hermite–Lindemann makes a candidate transcendental over $\mathbb{Q}$, hence over $\bar{\mathbb{Q}}$ (which is algebraic over $\mathbb{Q}$); in particular $u \notin \bar{\mathbb{Q}}$. The general statement `Diaz.no_vanishing_coeff` — which needs only $u \notin K$ and not transcendence — then applies with $K = \bar{\mathbb{Q}}$.
--
--   **Role.** This is the end-to-end form of the rigidity result over the base field the conjecture is actually about. Its hypotheses are the *arithmetic* ones a counterexample would satisfy — non-vanishing, algebraicity of $e^{u}$, algebraicity of the modulus — rather than a transcendence assumption that would have to be justified separately, and the base is $\bar{\mathbb{Q}}$ rather than an arbitrary subfield. Combined with $\det H(u,r) = 0$: the rows of a candidate's matrix are dependent over $\mathbb{C}$ while no coefficient of the associated bilinear form vanishes over $\bar{\mathbb{Q}}$ — the configuration at the boundary of the Matrix Coefficient Conjecture.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Instantiation.lean#L50-L66

import Mathlib
import Definitions.Def_Diaz_Instantiation
import Definitions.Def_Diaz_Rigidity

open ComplexConjugate
open Diaz

theorem Diaz.candidate_no_vanishing_coeff_Qbar
    {u r : ℂ} (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hr : r ∈ Qbar) (h : u * conj u = r ^ 2)
    (w v : Fin 2 → ℂ) (hwK : ∀ i, w i ∈ Qbar) (hvK : ∀ j, v j ∈ Qbar)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    ∑ i, ∑ j, w i * (Hmat u r) i j * v j ≠ 0 := by sorry
