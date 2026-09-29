-- Prove2me | Theorems.Thm_Diaz_pair_dichotomy_exclusive
-- name    : Diaz.pair_dichotomy_exclusive
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T12:13:00.199071+00:00
-- url     : https://prove2.me/theorems/99e66042-79f9-4b5d-a081-f97c074c1023
-- title:
--   Rational rays force algebraic dependence: exclusivity in the pair dichotomy
-- statement:
--   Let $u \in \mathbb{C}$ be such that $u\bar u$ is algebraic over $\mathbb{Q}$, and let $v$ be a non-zero rational multiple of either $u$ or $\bar u$:
--
--   $$v \;\in\; \mathbb{Q}^\times u \;\cup\; \mathbb{Q}^\times \bar u .$$
--
--   Then $u$ and $v$ are **algebraically dependent** over $\mathbb{Q}$.
--
--   **Where this sits.** This is the opening step of the proof of Carlo Perassi's pair dichotomy (rational proportionality or independence) — the clause that makes the dichotomy *exclusive*. The dichotomy asserts that for $u,v$ on the Diaz locus with $|v|^2/|u|^2 \in \mathbb{Q}$, **exactly one** of
--
--   * (i) $v \in \mathbb{Q}^\times u \,\dot\cup\, \mathbb{Q}^\times\bar u$,
--   * (ii) $u$ and $v$ are algebraically independent over $\mathbb{Q}$
--
--   holds. The implication (i) $\Rightarrow \neg$(ii) is this node, and it is **unconditional**: it uses no transcendence input whatever. The opposite direction $\neg$(ii) $\Rightarrow$ (i) is the deep half — it passes through Théorème 0.2 of Roy–Waldschmidt (1997), which is not available in this Mathlib revision, and then through the linear-algebra step already published as `Diaz.rational_singular_subspace_classification` and `Diaz.rational_subspace_quadric_ratios`. It also follows from Theorem 6.7 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.10, 27 September 2026, GitHub release note-v1.10), on this mission as the Proved node `DiazModulus.log_pair_rigid_of_trdeg_one`, because on the Diaz locus $\bar u = |u|^{2}/u$ and $\bar v = |v|^{2}/v$ with algebraic numerators, so $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(u,\bar u,v,\bar v) = \operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(u,v)$.
--
--   **Proof.** Write $q = u\bar u$.
--
--   *Case $v = cu$, $c \in \mathbb{Q}^\times$.* The non-zero polynomial $X_1 - cX_0 \in \mathbb{Q}[X_0,X_1]$ vanishes at $(u,v)$.
--
--   *Case $v = c\bar u$, $c \in \mathbb{Q}^\times$.* Then $uv = c\,u\bar u = cq$, which is algebraic over $\mathbb{Q}$ because $q$ is and $c$ is rational. Let $f = \operatorname{minpoly}_{\mathbb{Q}}(cq)$, a non-zero polynomial with $f(cq) = 0$, and set $P(X_0,X_1) = f(X_0X_1)$. Then
--
--   $$P(u,v) = f(uv) = f(cq) = 0 ,$$
--
--   and $P \neq 0$ because the substitution $T \mapsto X_0X_1$ is an injective $\mathbb{Q}$-algebra map $\mathbb{Q}[T] \to \mathbb{Q}[X_0,X_1]$ — it admits the left inverse $X_0 \mapsto T$, $X_1 \mapsto 1$, under which $T \mapsto X_0X_1 \mapsto T$.
--
--   In both cases a non-zero rational polynomial annihilates $(u,v)$, so the pair is not algebraically independent.
--
--   **Formalisation notes.** "Algebraically dependent over $\mathbb{Q}$" is rendered `¬ AlgebraicIndependent ℚ ![u, v]`. Two hypotheses of the original setting are deliberately **not** assumed, because the argument does not use them: $u \neq 0$ (the statement holds for $u = 0$ too, where $X_0$ itself annihilates the pair), and the algebraicity of $e^u$. Only $u\bar u \in \overline{\mathbb{Q}}$ is used, so the node applies verbatim off the Diaz locus.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node records one step of it in Lean and claims no novelty of its own. Elementary.
-- source:
--   Carlo Perassi, unpublished apart from this node: the clause that makes his pair dichotomy exclusive.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.pair_dichotomy_exclusive {u v : ℂ}
    (hq : IsAlgebraic ℚ (u * conj u))
    (h : (∃ c : ℚ, c ≠ 0 ∧ v = (c : ℂ) * u) ∨
         (∃ c : ℚ, c ≠ 0 ∧ v = (c : ℂ) * conj u)) :
    ¬ AlgebraicIndependent ℚ ![u, v] := by sorry
