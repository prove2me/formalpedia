-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_lemma_4_1
-- name    : BeckTeboulleMD.EMDA.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:30.796076+00:00
-- url     : https://prove2.me/theorems/cf7d672d-a13f-412b-b143-a595bfd8b467
-- title:
--   Lemma 4.1, p. 171 — B_ψ(c,a) + B_ψ(a,b) − B_ψ(c,b) = ⟨∇ψ(b) − ∇ψ(a), c − a⟩
-- statement:
--   This is the three-point identity of Chen and Teboulle.
--
--   Let $E$ be a real normed space, $S \subseteq E$ an open set with closure $\bar S$, and $\psi : E \to \mathbb R$ continuously differentiable on $S$. Let $B_\psi(x, y) = \psi(x) - \psi(y) - \langle x - y, \nabla\psi(y)\rangle$. Then for any $a, b \in S$ and $c \in \bar S$,
--   $$B_\psi(c, a) + B_\psi(a, b) - B_\psi(c, b) = \langle \nabla\psi(b) - \nabla\psi(a),\ c - a\rangle. \tag{4.14}$$
--
--   The identity generalises the Euclidean expansion of $\|c - a\|^2 + \|a - b\|^2 - \|c - b\|^2$ and is the key algebraic step of the convergence analysis of SANP.
--
--   **Formalization Note** $\nabla\psi(y)$ is the Fréchet derivative of $\psi$ at $y$, a continuous linear functional, and $\langle u, \nabla\psi(y)\rangle$ is its value at $u$. The hypotheses on $S$ and $\psi$ are those of the page.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 171, Lemma 4.1 (4.14)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Lemma 4.1 (Chen and Teboulle), p. 171, (4.14): the three-point identity
`B_ψ(c, a) + B_ψ(a, b) − B_ψ(c, b) = ⟨∇ψ(b) − ∇ψ(a), c − a⟩`
for `S` open, `ψ` continuously differentiable on `S`, `a, b ∈ S` and `c ∈ closure S`. -/
theorem lemma_4_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : IsOpen S) (ψ : E → ℝ) (hψ : ContDiffOn ℝ 1 ψ S)
    (a b c : E) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ closure S) :
    bregman ψ c a + bregman ψ a b - bregman ψ c b
      = (fderiv ℝ ψ b - fderiv ℝ ψ a) (c - a) := by sorry

end BeckTeboulleMD.EMDA
