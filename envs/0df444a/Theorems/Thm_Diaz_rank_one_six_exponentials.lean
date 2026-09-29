-- Prove2me | Theorems.Thm_Diaz_rank_one_six_exponentials
-- name    : Diaz.rank_one_six_exponentials
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:11:05.449658+00:00
-- url     : https://prove2.me/theorems/6a5f4f8a-4863-47d3-b408-4994dbf70a80
-- title:
--   A six-exponentials rank bound admits no rank-one witness
-- statement:
--   **Source.** Carlo Perassi's mathematics: the common engine of two statements of his, one on elliptic common multipliers in the complex multiplication
--   case and the other the first half of his p-adic multiplier bound for conjugate planes.
--
--   **Statement, as formalised.** Let `k ⊆ F` be fields and `V ⊆ F` a set. Suppose the
--   six-exponentials-type hypothesis
--
--   > every `2 × 3` matrix over `F` whose entries lie in `V`, whose rows are `k`-linearly
--   > independent and whose columns are `k`-linearly independent, has `F`-linearly independent
--   > rows (i.e. rank two).
--
--   Then there are no `a, b ∈ F` with `![a,b]` `k`-independent and no `y : Fin 3 → F`
--   `k`-independent such that all six products `a y_j`, `b y_j` lie in `V`.
--
--   **Why this is both statements.** Each of the two theorems produces a matrix that is an
--   **outer product** and derives a contradiction from the fact that a six-exponentials theorem
--   forces its rank to be two.
--
--   * The elliptic statement: `V = ℒ_E`, `k` the endomorphism field, `a = u`, `b = conj u` for `u` in the
--     elliptic Diaz locus, and `y_1,y_2,y_3` three `k`-independent common multipliers, i.e.
--     elements of `K^E_u = {y : uy ∈ ℒ_E and conj u · y ∈ ℒ_E}`. Rows are `k`-independent by
--     an axis alignment of his — on this mission, `Diaz.elliptic_axis_alignment`. The conclusion
--     `dim_k K^E_u ≤ 2` is exactly the non-existence of such a triple. The rank-two input is the
--     elliptic six exponentials corollary.
--   * The p-adic statement, first half: `F = ℂ_p`, `V = Λ_p = ℚ̄ + span_ℚ̄ ℒ_p`, `k = ℚ̄`, `a = 1`,
--     `b = x` for `x ∉ ℚ̄`, and `y_1,y_2,y_3` three `ℚ̄`-independent elements of
--     `M_x = {y ∈ Λ_p : xy ∈ Λ_p}`. Rows `![1,x]` are `ℚ̄`-independent precisely because
--     `x ∉ ℚ̄`. The conclusion `dim_ℚ̄ M_x ≤ 2` is again the non-existence of such a triple.
--     Here the rank-two input is the p-adic strong six exponentials theorem of Waldschmidt and
--     Roy, in the form of Corollary 2.2.2 of Maksoud.
--
--   Both deep inputs are unavailable — neither the elliptic nor the p-adic six exponentials
--   theorem is in Mathlib — so the rank bound is carried as the explicit hypothesis `hsix`, and
--   the citation boundary is visible in the statement. What is actually proved is the elementary
--   half: the matrix `(a y_j ; b y_j)` has `F`-dependent rows, since `b · (a y) − a · (b y) = 0`
--   and `(b, −a) ≠ 0`, while its rows and columns are `k`-independent whenever `![a,b]` and `y`
--   are. It is that clash, not the transcendence, that both proofs turn on.
--
--   **No new definition.** `ℒ_E` and `Λ_p` appear only as the arbitrary set `V`; the elliptic
--   apparatus and `ℂ_p` are absent.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9), which treats neither the elliptic nor the p-adic setting; it is unpublished apart from this node. It was left out for scope, not withdrawn as wrong.
--
--   **Novelty.** No novelty is claimed, either for the mathematics or for the formalisation.
--   Carlo Perassi presents this material as transfers of a complex argument to
--   another setting. The rank-one observation is elementary linear
--   algebra.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.rank_one_six_exponentials {F k : Type*} [Field F] [Field k] [Algebra k F]
    (V : Set F)
    (hsix : ∀ M : Fin 2 → Fin 3 → F, (∀ i j, M i j ∈ V) →
      LinearIndependent k M → LinearIndependent k (fun j i => M i j) →
      LinearIndependent F M)
    {a b : F} {y : Fin 3 → F}
    (hab : LinearIndependent k ![a, b]) (hy : LinearIndependent k y)
    (hV : ∀ j, a * y j ∈ V ∧ b * y j ∈ V) : False := by sorry
