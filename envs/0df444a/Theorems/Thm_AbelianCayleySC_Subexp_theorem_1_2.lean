-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_theorem_1_2
-- name    : AbelianCayleySC.Subexp.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:43:10.242634+00:00
-- url     : https://prove2.me/theorems/0ed37c3c-fc1a-4cbb-a8eb-a3b3f7da3271
-- title:
--   Theorem 1.2 — subexponential-time constant-factor approximation for sparsest cut on every finite abelian Cayley graph
-- statement:
--   There are universal constants $C,c>0$ and one algorithm such that the following holds. Let $G=\mathrm{Cay}(\Gamma,S)$ be an undirected abelian Cayley graph with $n=|\Gamma|\ge2$ vertices ($\Gamma$ any finite abelian group, $S=-S$, self-loops and disconnection allowed), presented only as a graph on the vertices $0,\dots,n-1$: neither the group, nor the labelling of the vertices by group elements, nor $S$ is given. The algorithm returns a set $Q$ of vertices with $\emptyset\ne Q\ne V$ and
--
--   $$\psi_G(Q)\le C\,\psi(G)$$
--
--   within
--
--   $$\exp\!\big(c\,n^{2/3}\big)$$
--
--   steps. Here $\psi_G(Q)=n|E(Q,V\setminus Q)|/(d|Q||V\setminus Q|)$ with $d=|S|$ the degree, and $\psi(G)$ is its minimum over proper non-empty $Q$.
--
--   This is the paper's main result: the first subexponential-time constant-factor approximation for sparsest cut on all finite abelian Cayley graphs, with no dependence on the number of generators.
--
--   **Formalization Note** The approximation and time constants trace back to the cited Theorem 2.1, whose constants the paper does not give; they are universal and chosen before $n$ and the graph. The degree enters as "for every $d$ such that $G$ is $d$-regular", which for $n\ge1$ is the single value $d=|S|$.
--
--   Differences from the source:
--   - encoding: "an algorithm" running "in time" a bound → one fixed Mathlib multi-stack Turing machine (TM2 over the alphabet Fin 4) that halts with the output word within the step bound; graph input as n² adjacency bits, output set as n indicator bits; reason: the paper names no machine model; the encodings are fixed in a definition, never a parameter
--   - reading: "in time O(exp(|Γ|^{2/3}))" → ∃ c > 0 universal: steps ≤ exp(c·n^{2/3}), n = |Γ|; reason: the paper fixes the meaning as exp(O(|Γ|^{2/3})): footnote 2 p.1 ("subexponential time means exp(O(n^δ))"), §2 p.3 ("|Γ|^{O(1)}·exp(O(|Γ|^{2/3}))") and §5 p.14 ("the total running time is exp(O(n^{2/3})), as desired"); the cited Theorem 2.1 has unspecified constants in the exponent
--   - reading: ψ(Q) ⩽ O(ψ(G)) for a non-empty Q ⊆ Γ → ∃ C > 0 universal: ψ_G(Q) ≤ C·ψ(G), with Q non-empty and Q ≠ V; reason: O(·) is a universal constant; ψ_G(Q) is defined only for proper Q (p.1)
--   - encoding: ψ(G) = min over ∅ ≠ Q ≠ V → hypothesis n ≥ 2; reason: for n = 1 the family of admissible cuts is empty and ψ(G) is undefined; the hypothesis excludes only that case
--   - encoding: G = Cay(Γ, S), vertex set Γ → a graph on {0,…,n−1} that is isomorphic, by an unknown bijection, to Cay(Γ, S) for some finite abelian Γ and symmetric S; reason: the algorithm is given only the graph (§2 p.3); a labelling of the vertices is the input format
--   - encoding: the degree d = |S| in ψ → ψ_G(Q) ≤ C·ψ(G) for every d such that G is d-regular; reason: for n ≥ 1 that d is unique and equals |S|
--   - encoding: graphs are d-regular with A(G) = (1/d)·adjacency, so |S| = 0 is outside the source's domain → |S| = 0 is admitted, with Lean's 1/0 = 0 and x/0 = 0; reason: the statement is true in that degenerate case and no instance with |S| ≥ 1 changes
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.2, Theorem 1.2 (proof §5, pp.13–14)

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin

open Finset

namespace AbelianCayleySC.Subexp

/-- **Theorem 1.2** (p.2), the main result. One fixed machine `M` and universal constants
`C, c > 0` such that, for every `n ≥ 2` and every graph on `Fin n` that is an undirected
abelian Cayley graph `Cay(Γ, S)` (only the graph is input: no group, labelling or `S`), `M` run
on the adjacency bits outputs the indicator bits of a non-empty proper `Q` with
`ψ_G(Q) ≤ C·ψ(G)`, for the degree `d` of the graph, within `exp(c·n^{2/3})` steps. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∃ M : Turing.TM2ComputableAux OnlineCRS.Combine.Sym OnlineCRS.Combine.Sym,
        ∀ n : ℕ, 2 ≤ n → ∀ (adj : Fin n → Fin n → Prop) [DecidableRel adj],
          IsAbelianCayley adj →
          ∃ Q : Finset (Fin n), Q.Nonempty ∧ Q ≠ univ ∧
            (∀ d : ℕ, IsRegular adj d → sparsity adj d Q ≤ C * sparsestCut adj d) ∧
            ∃ t : ℕ, (t : ℝ) ≤ Real.exp (c * (n : ℝ) ^ ((2 : ℝ) / 3)) ∧
              CFLOutliers.OutputsWithin M (encodeGraph adj) (encodeSet Q) t := by sorry

end AbelianCayleySC.Subexp
