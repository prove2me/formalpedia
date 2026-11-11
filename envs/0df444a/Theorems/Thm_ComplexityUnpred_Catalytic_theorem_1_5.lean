-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_theorem_1_5
-- name    : ComplexityUnpred.Catalytic.theorem_1_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:03:27.38195+00:00
-- url     : https://prove2.me/theorems/7f92a7f3-82da-49ab-99b3-22d00e97b506
-- title:
--   Theorem 1.5 — SearchCL reduces in polynomial time to UNPRED
-- statement:
--   A **search problem** is a relation $A\subseteq\{0,1\}^*\times\{0,1\}^*$; it is in **SearchCL** if one catalytic Turing machine with $O(\log n)$ work space and polynomial catalytic space, on every input $x$ and **every** initial catalytic tape $\tau$, halts with an output $y$ such that $(x,y)\in A$ and with $\tau$ restored on the catalytic tape. **UNPRED** asks, given $n$ and $\epsilon=1/r$ in unary and Boolean circuits $P_1,\dots,P_m$ (AND, OR, NOT, THRESHOLD gates) computing middle-bit predictors over $\{0,1\}^n$ at given indices, for a non-empty multiset $S\subseteq\{0,1\}^n$ on which every $P_j$ succeeds with probability less than $\frac12+\epsilon$. The theorem states
--   $$\textsf{SearchCL}\le_P\textsf{UNPRED}:$$
--   for every $A\in\textsf{SearchCL}$ there are deterministic polynomial-time maps $f$ and $g$ such that $f(x)$ is a valid UNPRED instance for every $x$, and $(x,g(x,S))\in A$ for **every** valid UNPRED answer $S$ of $f(x)$, however long $S$ is.
--
--   With Corollary 1.4 (UNPRED restricted to $\mathsf{TC}^1$ predictors is in SearchCL) it places the search version of the CL versus P question between two versions of UNPRED: $\textsf{UNPRED}\in\mathsf{FP}\Rightarrow\textsf{SearchCL}\subseteq\mathsf{FP}\Rightarrow\textsf{UNPRED}_{\mathsf{TC}^1}\in\mathsf{FP}$.
--
--   **Formalization Note** SearchCL is the published `InCL (fun _ => True) A` (every string an input), $\le_P$ the published `SearchReduces` with Cook-machine polynomial time; the source problem is $\langle$every string valid, $A\rangle$.
--
--   Differences from the source:
--   - generalization: SearchCL := ⋃_d SearchCSPACE[d log n, d n^d] (Definitions 2.6, 2.9, 2.10) → InCL (fun _ => True) A on the published binary machine: any polynomial catalytic length p ∈ ℕ[X], work ≤ C(⌊log₂(|x|+2)⌋+1) visited cells for some C ≥ 1; reason: InCL contains SearchCL (p := d X^d, C := d up to the constant-factor cost of a binary work alphabet), so the theorem specializes to the paper's class
--   - encoding: ≤P: both maps computable in deterministic polynomial time → CardinalMatching.SearchReduces with CookPvsNP.PolyTimeComputable (one-tape Cook machines, time |x|^k + k); the solution map reads the tagged pair (x, y); reason: the published platform reduction; it requires correctness for every answer, as §2.2 does
--   - encoding: UNPRED instances (n, r in unary, circuits, indices) and multiset answers, no code fixed → the codes UnpredInstance.encode and encStrings of the UNPRED definition; reason: one concrete prefix-free binary code, polynomially equivalent to any reasonable one
--   - reading: THRESHOLD gates with unspecified thresholds → gates Th_t (at least t inputs are 1), t in the gate label; reason: the paper does not fix the thresholds; Th_t is the standard reading and keeps the gate in the basis
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 2, Theorem 1.5

import Mathlib
import Definitions.Def_CatalyticMatching_General_CatalyticSpace
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_ComplexityUnpred_Catalytic_UNPRED

namespace ComplexityUnpred.Catalytic

/-- **Theorem 1.5** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 2): `SearchCL ≤_P UNPRED`. Every
search problem `A ⊆ {0,1}* × {0,1}*` computed by a catalytic logspace machine (for every input
`x` and every initial catalytic tape `τ` of the machine's polynomial length, the machine halts
with an output `y`, `(x, y) ∈ A`, and `τ` restored, using `O(log |x|)` work cells) reduces to
UNPRED by polynomial-time instance and solution maps, the solution map being correct for every
answer of UNPRED. SearchCL is read as the published `InCL (fun _ => True) A`, which contains
`⋃_d SearchCSPACE[d log n, d n^d]`. -/
theorem theorem_1_5 (A : List Bool → List Bool → Prop)
    (hA : CatalyticMatching.General.InCL (fun _ => True) A) :
    CardinalMatching.SearchReduces ⟨fun _ => True, A⟩ UNPRED := by sorry

end ComplexityUnpred.Catalytic
