-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_yannakakis_factorization
-- name    : ExtensionComplexity.TSP.yannakakis_factorization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:07:33.947238+00:00
-- url     : https://prove2.me/theorems/c60da668-eff7-42b4-8f9b-409ef18ed6cf
-- title:
--   Theorem 3 (Yannakakis) — $\mathrm{rank}_+(S)\le r$ iff an extension with $\le r$ facets iff an EF with $\le r$ inequalities
-- statement:
--   Let $P=\{x\in\mathbb R^{\iota} : Ax\le b\}=\mathrm{conv}(V)$ be a polytope with $A\in\mathbb R^{m\times\iota}$, $b\in\mathbb R^m$ and $V=\{v_1,\dots,v_N\}$, of dimension $\dim(P)\ge 1$, and let $S$ be the slack matrix of $P$ with respect to $Ax\le b$ and $V$. **Theorem 3** (Yannakakis 1991): for every positive integer $r$ the following are equivalent:
--
--   1. $\mathrm{rank}_+(S)\le r$;
--   2. $P$ has an extension of size at most $r$, i.e. a polytope $Q\subseteq\mathbb R^{e}$ with at most $r$ facets and a linear map $\pi$ with $\pi(Q)=P$;
--   3. $P$ has an EF of size at most $r$, i.e. with at most $r$ inequalities.
--
--   In short, $\mathrm{xc}(P)=\mathrm{rank}_+(S)$: lower bounds on extension complexity are lower bounds on the nonnegative rank of any slack matrix, and conversely.
--
--   **Formalization Note** $\mathbb R^d$ is $\mathbb R^{\iota}$ for a finite index type $\iota$. $\dim(P)\ge 1$ is stated as "$P$ contains two distinct points", which is equivalent for a nonempty convex set. The slack matrix is taken with respect to the given $A,b,V$ (not only facets and vertices). Condition 2 lets the ambient dimension $e$ of $Q$ be any natural number; condition 3 is "an EF of some size $r'\le r$".
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:10, Theorem 3

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix

open Matrix

namespace ExtensionComplexity.TSP

/-- **Theorem 3** [Yannakakis 1991] (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:10): let
`P = {x | Ax ≤ b} = conv(V)` be a polytope with `dim(P) ≥ 1`, and let `S` be the slack matrix of
`P` with respect to `Ax ≤ b` and `V`. For every positive integer `r` the following are equivalent:
(i) `rank₊(S) ≤ r`; (ii) `P` has an extension with at most `r` facets; (iii) `P` has an EF with at
most `r` inequalities. `dim(P) ≥ 1` is stated as: `P` contains two distinct points. -/
theorem yannakakis_factorization {ι : Type*} [Fintype ι] {m N : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (V : Fin N → ι → ℝ) (P : Set (ι → ℝ))
    (hPA : P = {x | A *ᵥ x ≤ b}) (hPV : P = convexHull ℝ (Set.range V))
    (hdim : ∃ x ∈ P, ∃ y ∈ P, x ≠ y) (r : ℕ) (hr : 1 ≤ r) :
    List.TFAE
      [nonnegRank (slackMatrix A b V) ≤ r,
       ∃ (e : ℕ) (Q : Set (Fin e → ℝ)), IsExtension Q P ∧ HasAtMostFacets Q r,
       ∃ r' ≤ r, IsEFOfSize P r'] := by sorry

end ExtensionComplexity.TSP
