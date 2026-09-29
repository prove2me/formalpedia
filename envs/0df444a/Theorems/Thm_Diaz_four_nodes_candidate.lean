-- Prove2me | Theorems.Thm_Diaz_four_nodes_candidate
-- name    : Diaz.four_nodes_candidate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:08.162727+00:00
-- url     : https://prove2.me/theorems/6f338e64-261b-4533-b300-c115e5c81804
-- title:
--   Four nodes, for a Diaz candidate over an algebraic base
-- statement:
--   Let $L \subseteq \mathbb{C}$ be a subfield algebraic over $\mathbb{Q}$, and let $u \in \mathbb{C}$ be a **candidate**: $u \neq 0$ and $e^{u}$ algebraic over $\mathbb{Q}$, with $u\bar u \in L$. Let $a, b \in \mathbb{Q}$ and put $v = a u + b\bar u$. If
--
--   $$v\,\bar v  =  u\,\bar u,$$
--
--   then $(a,b) \in \{(1,0), (-1,0), (0,1), (0,-1)\}$.
--
--   **Why.** This is `Diaz.four_nodes` with its transcendence input supplied. That input is $(u+\bar u)^{2} \notin L$, and for a candidate it follows from Hermite–Lindemann: $u + \bar u$ is non-zero (the axis lemma `Diaz.not_on_axes`), its exponential $e^{u+\bar u} = e^{u}\,\overline{e^{u}}$ is algebraic, so $u+\bar u$ is itself transcendental over $\mathbb{Q}$ and hence over $L$; a transcendental element has no square in the base field.
--
--   **Role.** The hypotheses here are the *arithmetic* ones — non-vanishing, algebraicity of $e^{u}$, algebraicity of the modulus — rather than transcendence, so this is the form in which the four-node statement actually applies to a hypothetical counterexample to Diaz's modulus conjecture. The set $\{\, u, -u, \bar u, -\bar u \,\}$ is exactly the orbit of $u$ under the two involutions $z \mapsto -z$ and $z \mapsto \bar z$, so the circle carries no *unexpected* rational-plane point: another configuration a proof strategy might have hoped to exploit is not there.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Nodes.lean#L177-L207

import Mathlib

open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

theorem Diaz.four_nodes_candidate {L : Subfield ℂ} [Algebra.IsAlgebraic ℚ (↥L)]
    (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hρ : u * conj u ∈ L)
    {a b : ℚ} (h : ((a : ℂ) * u + (b : ℂ) * conj u)
      * conj ((a : ℂ) * u + (b : ℂ) * conj u) = u * conj u) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0)
      ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by sorry
