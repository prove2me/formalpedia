-- Prove2me | Theorems.Thm_Erdos180_quantitativeCompactnessCounterexample
-- name    : Erdos180.quantitativeCompactnessCounterexample
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:23:09.604149+00:00
-- url     : https://prove2.me/theorems/221c059b-9b90-4ce0-a347-eb438f63003c
-- title:
--   Failure of compactness: a quantitative counterexample (Theorem 1.1)
-- statement:
--   There exist a finite nonempty family $\mathcal{F}$ of graphs, each connected, bipartite
--   and containing a cycle, and constants $c, C > 0$, such that
--
--   $$\mathrm{ex}(n, F) \;\ge\; c\, n^{4/3} \quad (F \in \mathcal{F}) \qquad\text{and}\qquad
--   \mathrm{ex}(n, \mathcal{F})^{16} \;\le\; C\, n^{21},$$
--
--   where $21/16 = 4/3 - 1/48$. In particular $\mathcal{F}$ is not compact, and the
--   Erdős-Simonovits compactness conjecture is false.
--
--   This is Theorem 1.1 of the source, in the explicit form the formalisation establishes: the
--   family bound $O(n^{4/3 - 1/48})$ and the uniform member bound $\Omega(n^{4/3})$ are separated by
--   a polynomial factor $n^{1/48}$, so no member can dominate the family up to a constant. The
--   family is $\mathcal{F} = \{C_4, C_6\} \cup \mathcal{J} \cup \mathcal{K}$ (Definition 2.5); the
--   upper bound is Proposition 3.4, proved by counting short paths in an $\mathcal{F}$-free graph,
--   and the lower bound is Proposition 4.3, witnessed by incidence graphs of symplectic generalized
--   quadrangles whose characteristic is chosen to suit the forbidden member. Compare Conlon,
--   Mulrenin and Pohoata, who disproved Verstraëte's stronger host-graph analogue for even cycles
--   without resolving compactness itself.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9320-L9346

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Real.Basic

open Erdos180
open Finset SimpleGraph
open scoped Classical

theorem Erdos180.quantitativeCompactnessCounterexample :
    ∃ (family : Finset FiniteGraph) (c C : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      0 < C ∧
      UniformMemberLower family c ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree family host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal family n : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by sorry
