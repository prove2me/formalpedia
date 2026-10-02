-- Prove2me | Theorems.Thm_Disjunctive_Dominants_general_dominant_facet_characterization
-- name    : Disjunctive.Dominants.general_dominant_facet_characterization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:10:43.591187+00:00
-- url     : https://prove2.me/theorems/32e1104e-5adb-4078-822d-4ad8890f6ee3
-- title:
--   Theorem 13.7 — the general facet characterization of the dominant
-- statement:
--   This is Theorem 13.7 of Balas's *Disjunctive Programming*, the goal theorem of this mission:
--   a **complete, minimal, facet-exact** description of the dominant of an arbitrary polytope
--   (not necessarily upper monotone), generalizing Theorem 13.3 from a single inequality to any
--   polytope $P$.
--
--   Let $I^S$ be the set of valid inequalities $\pi x\ge1$ of the projection $P^S$ with $\pi_j>0$
--   for every $j\in S$ (and $\pi_j=0$ off $S$) that are satisfied at equality by $|S|$ linearly
--   independent points of $P^S$. Then
--   $$
--   P^+ = \{x\ge0 : \pi x\ge1 \text{ for every } S\subseteq N \text{ and } \pi\in I^S\},
--   $$
--   and **every** such inequality is facet-defining for $P^+$.
--
--   The book's proof (forward direction): any $\pi\in I^S$ is valid for $P^S$ hence for $P^+$; the
--   $|S|$ tight points of $P^S$ lift to points of $P$ (via the projection), and together with
--   $n-|S|$ further points obtained by adding unit vectors $e_j$ ($j\notin S$) to one of them, give
--   $n$ linearly independent points of $P^+$ tight at $\pi x=1$, so $\pi x\ge1$ is facet-defining.
--   (Converse): given a facet $\pi x\ge1$ of $P^+$ with support $S$, if fewer than $|S|$ linearly
--   independent extreme points of $P^S$ achieve equality, a perturbation argument along a vector
--   $\alpha$ vanishing on the tight points produces two distinct valid inequalities averaging to
--   $\pi x\ge1$, contradicting facetness.
--
--   **Formalization Note.** `IsInIS` packages membership in $I^S$ exactly as printed: support
--   exactly $S$ (`π_j=0` off `S`, `π_j>0` on `S`), validity for `P^S`, and existence of `|S|`
--   linearly independent tight points of `P^S`. The conclusion is stated as two conjuncts, matching
--   the theorem's own "and each of these inequalities is facet-defining" — a set-equality claim
--   together with a per-inequality facet claim, not collapsed into one.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 219-220, Theorem 13.7

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Theorem 13.7 (Balas §13.2, p. 219-220), the goal theorem of this mission: `P⁺ = {x≥0 :
πx≥1 for every S⊆N and π∈I^S}`, and every such inequality is facet-defining for `P⁺`. `P` is nonempty: for `P = ∅` the only `π ∈ I^S` is `π = 0` at `S = ∅`, and the claimed facet
is the empty set. -/
theorem general_dominant_facet_characterization {n : ℕ} (P : Set (Fin n → ℝ))
    (hP : P.Nonempty) :
    Dominant P = {x | 0 ≤ x ∧ ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        1 ≤ dotProduct pi x} ∧
      ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = 1}) := by sorry

end Disjunctive.Dominants
