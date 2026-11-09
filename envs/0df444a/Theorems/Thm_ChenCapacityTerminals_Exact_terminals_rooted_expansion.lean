-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_terminals_rooted_expansion
-- name    : ChenCapacityTerminals.Exact.terminals_rooted_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:52.745238+00:00
-- url     : https://prove2.me/theorems/e0142f0e-48c9-4c7b-9a06-28a0d0cd90f8
-- title:
--   Theorem 2.1 — Terminals and rooted expansion
-- statement:
--   Let a prepared rooted integer-capacity graph have $n\ge2$ vertices and $m$ arcs. Give each vertex a nonnegative integer mass $b(v)$ with total $W>0$. For every $1\le d\le n$, integer $t\ge1$ and rational $L>0$, one deterministic bounded-word program constructs $P\subseteq V\setminus\{r\}$ such that
--   $$|P|\le C\frac nd\log(2+m)+\frac W{t+1}.$$
--   Here $C>0$ is absolute and the coefficient of $W/(t+1)$ is exactly one. Every legal tie choice in the construction has the same guarantee. If $L\le\lambda$, then for every $X\subseteq V\setminus(P\cup\{r\})$,
--   $$b(X)\le C_dt\frac{f(X)}L,\qquad C_d=4d(3+\lceil\log_2n\rceil).$$
--   For unit masses and $t=d$, this explicitly yields $|X|\le C_ddf(X)/L$. Construction time is $\widetilde O(d(m+n))$ for every guess, on every fixed polynomial class of capacities, input size, $t,W$ and the numerator and denominator of $L$.
--
--   This theorem supplies both the weighted separator and its executable construction, with no good-scale hypothesis on its size or running time.
--
--   Differences from the source:
--   - encoding: finite vertex labels and original arc identities → canonical labels 0,...,n-1 for machine inputs, arbitrary finite natural labels for structural statements, and ordered arc records; reason: finite relabeling preserves every instance; arc positions preserve multiplicities
--   - encoding: L ≤ λ for the rooted minimum λ → every nonempty root-avoiding shore has entering capacity at least L; reason: this is the same lower-bound assertion without choosing an optimizer or taking a default-valued infimum
--   - encoding: the legal SCC, cover and guide choices in Sections 2.1–2.3 → LegalConstruction records the full recipe including a postorder extension for arbitrary masses; reason: every legal guide has this extension; no size, expansion or time conclusion is assumed
--   - encoding: O and soft-O resource guarantees → positive constants and logarithm exponents quantified before the instances; actual finite-program executions and network traces; reason: uniform constants replace asymptotic notation without fixing an unsupported numeral or granting free graph operations
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 3, PDF p. 4, Theorem 2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=4

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

theorem terminals_rooted_expansion :
    ∃ C : ℝ, ∃ P : List TrulySubcubicAPSP.Instr, 0 < C ∧ TerminalTime P ∧
      ∀ (G : IntegerInput) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ),
        TerminalParameters G r d L b t →
        (∃ c, LegalConstruction G.network r d L b t c) ∧
        ∀ c, LegalConstruction G.network r d L b t c → TerminalShape C G.network r d L b t c := by sorry

end ChenCapacityTerminals.Exact
