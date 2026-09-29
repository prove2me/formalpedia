-- Prove2me | Theorems.Thm_Diaz_axis_triple_indep
-- name    : Diaz.axis_triple_indep
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:27.68458+00:00
-- url     : https://prove2.me/theorems/5df4e179-138d-4898-948d-ae6f456ef3eb
-- title:
--   An axis-parallel pair of unequal modulus has independent coordinates
-- statement:
--   Let $u \neq 0$ with $e^{u}$ and $u\bar u$ algebraic — a Diaz candidate. Let $\tau$ be real or purely imaginary ($\bar\tau = \pm\tau$), put $v = u + \tau$, and suppose $v\bar v$ is algebraic but $v\bar v \neq u\bar u$, i.e. $|v| \neq |u|$. Then $u$, $\bar u$, $\tau$ are linearly independent over $\mathbb{Q}$.
--
--   **Where this sits.** This is the linear-independence half of the last assertion of Carlo Perassi's axis-parallel rational-ratio rigidity theorem: "If these conditions fail, then $u, \bar u, \tau$ are $\mathbb{Q}$-linearly independent". The conditions that fail are the equivalent (i)–(iii), of which (ii) is $|v| = |u|$; that is the hypothesis `hne`.
--
--   **Proof.** Hermite–Lindemann puts $u$ off both coordinate axes, so $u \neq \bar u$ and $u + \bar u \neq 0$. Conjugating the rational relation and combining with it kills $\tau$ and forces $a = b$ in the real case and $a = -b$ in the imaginary case, leaving
--
--   $$a(u + \bar u) + c\tau = 0 \qquad \text{resp.} \qquad a(u - \bar u) + c\tau = 0 .$$
--
--   If $c = 0$ this gives $a = b = 0$ at once. If $c \neq 0$ then $\tau = r(u \pm \bar u)$ with $r = -a/c \in \mathbb{Q}$, and a direct expansion gives the identity
--
--   $$v\bar v - u\bar u = r(1+r)(u+\bar u)^{2} \qquad \text{resp.} \qquad v\bar v - u\bar u = -r(1+r)(u-\bar u)^{2}.$$
--
--   If $r(1+r) = 0$ the two moduli agree, against `hne`. Otherwise $(u \pm \bar u)^{2}$ is algebraic, hence so is $u \pm \bar u$; it is non-zero, and its exponential $e^{u}e^{\pm\bar u}$ is algebraic, so Hermite–Lindemann is contradicted.
--
--   **What the hypotheses do and do not say.** The theorem takes $\tau = v - u$ with $v$ a second candidate, so $\tau$ is itself a non-zero logarithm. The proof never uses that: neither $\tau \neq 0$ nor algebraicity of $e^{\tau}$ appears, and both have been dropped. What is used about $v$ is only that $v\bar v$ is algebraic and differs from $u\bar u$.
--
--   **What is deliberately not claimed.** The equivalence (i) $\Leftrightarrow$ (ii) $\Leftrightarrow$ (iii) of that theorem, and the quadratic non-vanishing $P(u,\bar u,\tau) \neq 0$, both rest on Theorem 0.2 of Roy–Waldschmidt, which is not available in Mathlib. They are not published.
--
--   Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.axis_triple_indep {u τ : ℂ}
    (hu0 : u ≠ 0) (hexpu : IsAlgebraic ℚ (Complex.exp u))
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hax : conj τ = τ ∨ conj τ = -τ)
    (hq : IsAlgebraic ℚ ((u + τ) * conj (u + τ)))
    (hne : (u + τ) * conj (u + τ) ≠ u * conj u)
    {a b c : ℚ} (hrel : (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * τ = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by sorry
