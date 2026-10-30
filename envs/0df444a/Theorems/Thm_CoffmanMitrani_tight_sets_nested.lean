-- Prove2me | Theorems.Thm_CoffmanMitrani_tight_sets_nested
-- name    : CoffmanMitrani.tight_sets_nested
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:29:05.138004+00:00
-- url     : https://prove2.me/theorems/5a81ea39-e899-47c8-b481-1a6e45962693
-- title:
--   Proof of Lemma 2: the tight sets are nested
-- statement:
--   Let $\hat W \in H^{**}$ and let $g_1, g_2$ be nonempty sets of classes for which (5) holds, i.e.
--   $$\sum_{i\in g_j}\rho_i \hat W_i = \frac{\sum_{i\in g_j}\rho_i/\mu_i}{1-\sum_{i\in g_j}\rho_i}, \qquad j = 1,2.$$
--   Then $g_1 \subseteq g_2$ or $g_2 \subseteq g_1$.
--
--   Applied to the $M$ different sets $g_1,\dots,g_M$ of a vertex, this says that they are strictly included in each other, i.e. they form a chain $\{i_1\} \subset \{i_1,i_2\} \subset \dots \subset \{1,\dots,M\}$.
--
--   Differences from the source:
--   - encoding: classes 1, …, M and the nth arriving job of class i → classes Fin M and job index n : ℕ, both 0-based; reason: Lean indexing; the same objects
--   - encoding: M classes, Poisson rates λi, exponential parameters μi, equilibrium assumed (ρ < 1) → Data with 1 ≤ M, 0 < λi, 0 < μi and Σ λi/μi < 1; reason: the rates of a Poisson stream and of an exponential law are positive, M = 0 has no classes, and ρ < 1 is the paper's standing equilibrium assumption (pp. 812–813)
--   - generalization: Ŵ a vertex of H** and g1, …, gM the M sets of its system (5) → any Ŵ ∈ H** and any two nonempty sets on which (4) holds with equality; reason: the paper's argument uses only Ŵ ∈ H** and the two equations; a vertex and its sets are a special case
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2

import Mathlib
import Definitions.Def_CoffmanMitrani_Hss

namespace CoffmanMitrani

/-- **The tight sets of a point of `H**` are nested.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2: "Let Ŵ = (Ŵ1, Ŵ2, ···, ŴM) be a vertex of H**. It satisfies,
therefore a system of M equations Σ_{i∈gj} ρi Ŵi = (Σ_{i∈gj} ρi/μi)/(1 − Σ_{i∈gj} ρi);
j = 1, 2, ···, M (5) where one of the gj is the set {1, 2, ···, M} and the others are proper,
nonempty and different subsets. We shall demonstrate that all these subsets are strictly included
in each other."

If `W ∈ H**` and `g1`, `g2` are nonempty sets of classes on which (4) holds with equality, then
`g1 ⊆ g2` or `g2 ⊆ g1`.

**Formalization Note.** Stated for every point of `H**` and every pair of tight sets, not only for
vertices; the paper's argument uses only `Ŵ ∈ H**` and the two equations. For distinct sets the
conclusion is the paper's strict inclusion. -/
theorem tight_sets_nested (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Hss D)
    (g1 g2 : Finset (Fin D.M)) (hg1 : g1.Nonempty) (hg2 : g2.Nonempty)
    (ht1 : ∑ i ∈ g1, D.rho i * W i = D.loadBound g1)
    (ht2 : ∑ i ∈ g2, D.rho i * W i = D.loadBound g2) :
    g1 ⊆ g2 ∨ g2 ⊆ g1 := by sorry

end CoffmanMitrani
