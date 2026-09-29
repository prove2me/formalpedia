-- Prove2me | Theorems.Thm_DiazModulus_candidate_exp_angularTriple_transcendental
-- name    : DiazModulus.candidate_exp_angularTriple_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T17:55:49.108396+00:00
-- url     : https://prove2.me/theorems/cb4de219-9257-4b1b-96a9-1eb661607bde
-- title:
--   At a candidate, $e^{u^{2}/\bar{u}}$ is transcendental
-- statement:
--   **At a candidate, the third angular exponential is transcendental.**
--
--   Let $u$ be a *candidate* for a counterexample to Diaz's modulus conjecture: $u \neq 0$, $|u|$
--   algebraic, and $e^{u}$ algebraic. Then $e^{u^{2}/\bar{u}}$ is transcendental.
--
--   **The argument.** Put $c = u\bar{u} = |u|^{2}$, which is non-zero and algebraic, and $t = u^{2}/c$.
--   Feed the six exponentials theorem — the mission's `DiazModulus.six_exponentials` — the two families
--   $x = (u, \bar{u})$ and $y = (1, t, t^{-1})$. Their product matrix is
--   $$\begin{pmatrix} u & u^{3}/c & \bar{u} \\ \bar{u} & u & \bar{u}^{2}/u \end{pmatrix},$$
--   because $u\,t^{-1} = c/u = \bar{u}$ and $\bar{u}\,t = u$. Here $u^{3}/c = u^{2}/\bar{u}$ is the
--   exponent in the statement, and $\bar{u}^{2}/u$ is its complex conjugate.
--
--   Both independence hypotheses come from Hermite–Lindemann, which makes $u$ transcendental (the
--   mission's `DiazModulus.hermite_lindemann_holds`, applied to the algebraic value $e^{u}$). A rational
--   relation between $u$ and $\bar{u}$ would make $u/\bar{u} = u^{2}/c$ rational, hence $u^{2}$ and then
--   $u$ algebraic. A rational relation among $1, t, t^{-1}$, multiplied by $t$, is a non-zero rational
--   polynomial of degree at most $2$ vanishing at $t$; but $t$ is transcendental too, since $u^{2} = ct$
--   would otherwise be algebraic.
--
--   Four of the six entries are $u$ or $\bar{u}$, whose exponentials are algebraic by the candidate
--   hypothesis together with the stability of algebraicity under complex conjugation. So if
--   $e^{u^{2}/\bar{u}}$ were algebraic, its conjugate $e^{\bar{u}^{2}/u}$ would be as well, all six
--   would be algebraic, and the six exponentials theorem would be contradicted.
--
--   **Attribution — this is not new, and what is known is stronger.** Guy Diaz, *Produits et quotients de
--   combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels*,
--   J. Théor. Nombres Bordeaux **19** (2007), 373–391, proves in **théorème 7(1)**, p. 390: for
--   $u, v \in \mathbb{C}$ with $(1, u, \bar{u})$ and $(v, \bar{v})$ both $\bar{\mathbb{Q}}$-linearly
--   independent, $\{v,\ vu,\ v\bar{u}\} \not\subset \tilde{\mathcal{L}}$. Taking $v := u$ and his
--   $u := u/\bar{u}$ turns this into $\{u,\ u^{2}/\bar{u},\ \bar{u}\} \not\subset
--   \tilde{\mathcal{L}}$. For a candidate both of his hypotheses hold, by the same Hermite–Lindemann
--   argument recalled above, so his theorem applies and yields strictly more than the statement here: it
--   places $u^{2}/\bar{u}$ outside $\tilde{\mathcal{L}}$, the $\bar{\mathbb{Q}}$-span of
--   $\{1\} \cup \mathcal{L}$, which properly contains $\mathcal{L}$ (it contains $1$, and
--   $1 \notin \mathcal{L}$ because $e$ is transcendental); and his hypotheses do not require $|u|$ to be
--   algebraic. Diaz derives it from the **strong** six exponentials theorem.
--
--   **No novelty is claimed for this node.** The one thing observed here is about implementation, not
--   about transcendence: for the weaker conclusion — membership in $\mathcal{L}$ rather than in
--   $\tilde{\mathcal{L}}$ — the **ordinary** six exponentials theorem already suffices, so the node
--   closes from material the mission already carries, with no appeal to the strong form.
--
--   **Role in the mission.** This is the first genuine consequence drawn from `six_exponentials` here. It
--   does not settle the conjecture at $u$ — that would need $e^{u}$ itself to be transcendental — but it
--   records one more constraint every candidate must satisfy: a candidate cannot have all three of $u$,
--   $\bar{u}$ and $u^{2}/\bar{u}$ in $\mathcal{L}$.
-- source:
--   G. Diaz, Produits et quotients de combinaisons lineaires de logarithmes de nombres algebriques : conjectures et resultats partiels, J. Theor. Nombres Bordeaux 19 (2007), 373-391, theoreme 7(1), p. 390 (a stronger statement, proved there from the strong six exponentials theorem)

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem candidate_exp_angularTriple_transcendental
    {u : ℂ} (h : IsCandidate u) :
    Transcendental ℚ (Complex.exp (u ^ 2 / conj u)) := by sorry
end DiazModulus
