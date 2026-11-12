-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_theorem_2_1
-- name    : AbelianCayleySC.Subexp.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:43:23.45395+00:00
-- url     : https://prove2.me/theorems/7c13ac13-d556-4282-bbbb-eada3272b623
-- title:
--   Theorem 2.1 [GS13] — eigenspace enumeration: constant-factor sparsest cut in time $n^{O(1)}\exp(O(\mathrm{mul}_{128\phi(G)}(G)))$
-- statement:
--   There are universal constants $C,c>0$ and one algorithm such that, for every $n\ge2$ and every undirected $d$-regular graph $G$ on $n$ vertices ($d\ge1$, self-loops allowed), given only $G$, the algorithm returns a set $Q$ of vertices with $\emptyset\ne Q\ne V$ and
--
--   $$\psi_G(Q)\le C\,\psi(G),$$
--
--   within
--
--   $$c\,n^{c}\exp\!\big(c\cdot\mathrm{mul}_{128\phi(G)}(G)\big)$$
--
--   steps, where $\mathrm{mul}_{\tau}(G)$ counts the eigenvalues of $L(G)$ at most $\tau$ with multiplicity and $\phi(G)$ is the conductance of $G$.
--
--   The paper cites this guarantee from Guruswami–Sinop [GS13], with the formal statement in [dJR+25], and does not prove it; its proof of Theorem 1.2 uses it in Cases 1 and 3.
--
--   **Formalization Note** The paper writes $n^{O(1)}\cdot\exp(O(\cdot))$ and "constant-factor"; these are universal constants $c$ and $C$, chosen before $n$, the graph and its degree.
--
--   Differences from the source:
--   - encoding: "an algorithm" running "in time" a bound → one fixed Mathlib multi-stack Turing machine (TM2 over the alphabet Fin 4) that halts with the output word within the step bound; graph input as n² adjacency bits, output set as n indicator bits; reason: the paper names no machine model; the encodings are fixed in a definition, never a parameter
--   - reading: "constant-factor approximation algorithm for sparsest cut" with time n^{O(1)}·exp(O(mul_{128φ(G)}(G))) → ∃ C, c > 0 universal, chosen before the machine's input: ψ_G(Q) ≤ C·ψ(G) and steps ≤ c·n^c·exp(c·mul_{128φ(G)}(G)); reason: the paper's O(·) and "constant-factor" are universal constants; "sparsest cut" is the ψ objective of p.1
--   - reading: an approximation algorithm "finds" a cut → the output Q is non-empty and Q ≠ V; reason: ψ_G(Q) is defined only for proper non-empty Q
--   - encoding: ψ(G) = min over ∅ ≠ Q ≠ V → hypothesis n ≥ 2; reason: for n = 1 the family of admissible cuts is empty and ψ(G) is undefined; the hypothesis excludes only that case
--   - encoding: "regular graph" (§3: undirected, d-regular, self-loops allowed; A(G) = (1/d)·adjacency) → hypotheses: symmetric adjacency, every vertex has exactly d neighbours, d ≥ 1; vertices labelled 0,…,n−1; reason: d ≥ 1 excludes only the case where A(G) is undefined; the labelling is the input format
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.3, Theorem 2.1 (cited from [GS13], formal guarantee in [dJR+25])

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin

open Finset

namespace AbelianCayleySC.Subexp

/-- **Theorem 2.1** [GS13] (p.3). One fixed machine `M` and universal constants `C, c > 0` such
that, for every `n ≥ 2` and every undirected `d`-regular graph `G` on `Fin n` (loops allowed,
`d ≥ 1`), `M` run on the adjacency bits of `G` outputs the indicator bits of a non-empty proper
`Q` with `ψ_G(Q) ≤ C·ψ(G)` within `c·n^c·exp(c·mul_{128φ(G)}(G))` steps. -/
theorem theorem_2_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∃ M : Turing.TM2ComputableAux OnlineCRS.Combine.Sym OnlineCRS.Combine.Sym,
        ∀ n : ℕ, 2 ≤ n → ∀ (adj : Fin n → Fin n → Prop) [DecidableRel adj]
          (hsymm : IsUndirected adj) (d : ℕ), 1 ≤ d → IsRegular adj d →
          ∃ Q : Finset (Fin n), Q.Nonempty ∧ Q ≠ univ ∧
            sparsity adj d Q ≤ C * sparsestCut adj d ∧
            ∃ t : ℕ,
              (t : ℝ) ≤ c * (n : ℝ) ^ c *
                Real.exp (c * (mulLap adj hsymm d (128 * conductance adj d) : ℝ)) ∧
              CFLOutliers.OutputsWithin M (encodeGraph adj) (encodeSet Q) t := by sorry

end AbelianCayleySC.Subexp
