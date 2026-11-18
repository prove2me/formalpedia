-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_exact_binary_oracle_feasibility
-- name    : EdgeSublinearMWIS.Main.exact_binary_oracle_feasibility
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T00:09:47.460194+00:00
-- url     : https://prove2.me/theorems/15de4fff-5724-460a-a805-592c8f4a1ea7
-- title:
--   Exact finite-program oracle feasibility for well-described binary hulls
-- statement:
--   Fix a polynomial $b$ that bounds the encoding length of every inequality in some rational description of each binary hull, in every dimension. There is one finite deterministic oracle-feasibility program with polynomial bounds on its query count, execution time and rational query encoding length. For every fixed hull $P=\operatorname{conv}(V)$, where $V\subseteq\{0,1\}^d$, and every admissible transcript of strict separating inequalities valid on $P$ and having length at most $b(d+1)$, the program either correctly declares $P$ empty or produces its next rational query. At the prescribed polynomial query limit, a produced query belongs to $P$.
--
--   Thus exact feasibility, including empty and lower-dimensional hulls, admits
--
--   $$\text{polynomial query count, polynomial bit work, and polynomial query length.}$$
--
--   The polynomial bounds and program are fixed before the dimension, target hull and transcript. This is the computational part of the exact ellipsoid interface; the polynomial halfspace-description bound is supplied separately.
--
--   **Formalization Note** A query is an actual output of the finite stack program on the serialized transcript. The work bound covers replaying the transcript from the initial state.
-- source:
--   Groetschel, Lovasz and Schrijver, Geometric Algorithms and Combinatorial Optimization (1988), https://www.zib.de/userpage/groetschel/pubnew/paper/groetschellovaszschrijver1988.pdf, Theorem 6.4.1 and proof pp.174–178, including exact feasibility in proper affine subspaces; rounded implementation Section 3.1 pp.80–82. Specialization to binary hulls with the mission transcript interface.

import Definitions.Def_EdgeSublinearMWIS_Main_Ellipsoid

theorem EdgeSublinearMWIS.Main.exact_binary_oracle_feasibility (bound : Polynomial ℕ) (hbound : EdgeSublinearMWIS.Main.BinaryHullDescriptions bound) : ∃ (E : EdgeSublinearMWIS.Main.Program) (queries work coordinates : Polynomial ℕ), EdgeSublinearMWIS.Main.ExactEllipsoid E bound queries work coordinates := by sorry
