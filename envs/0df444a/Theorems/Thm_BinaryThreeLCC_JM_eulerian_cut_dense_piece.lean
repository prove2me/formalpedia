-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_eulerian_cut_dense_piece
-- name    : BinaryThreeLCC.JM.eulerian_cut_dense_piece
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:22.191809+00:00
-- url     : https://prove2.me/theorems/64f902cd-e7a4-588a-994c-e65c1d2c7ff0
-- title:
--   An Eulerian cut-dense piece in a digraph of linear minimum out-degree (Lemma 4.2, variant)
-- statement:
--   Let $R$ be a binary relation on a finite type $\alpha$, let $V\subseteq\alpha$ be nonempty with $|V|\le N$, and let $\theta>0$. Suppose every $x\in V$ has at least $\theta N$ out-neighbours inside $V$. Then there exist a nonempty $U\subseteq V$ and a finite set $F\subseteq U\times U$ of arcs of $R$ such that
--
--   1. $|U|\ge \theta^2N/16$;
--   2. $F$ is Eulerian: every vertex has equally many arcs of $F$ leaving it and entering it;
--   3. $F$ is $\lambda$-cut-dense on $U$ with $\lambda=\theta^3/64$: for every $S\subseteq U$,
--   $$\bigl|\{(x,y)\in F:\ x\in S,\ y\in U\setminus S\}\bigr|\ \ge\ \frac{\theta^3}{64}\,|S|\,|U\setminus S| .$$
--
--   This is the Eulerian expanding subgraph used in the proof of Theorem 1 (Lemma 4.2 of the source), with explicit constants. The proof follows the source: extract arc-disjoint short cycles covering many arcs, then split along sparse cuts while deleting whole cycles so that every piece stays Eulerian. Short cycles come from the Chvátal–Szemerédi theorem, which gives length $O(1/\theta)$.
-- source:
--   Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf, Lemma 4.2 and its proof §4.1 (printed pp. 11–13); variant with cycle length O(1/θ) from Chvátal–Szemerédi instead of Fact 3.4

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

theorem eulerian_cut_dense_piece {α : Type} [Fintype α] [DecidableEq α]
    (V : Finset α) (R : α → α → Prop) [DecidableRel R] (N : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (hV0 : V.Nonempty) (hV : V.card ≤ N)
    (hdeg : ∀ x ∈ V, θ * N ≤ ((V.filter (fun y => R x y)).card : ℝ)) :
    ∃ (U : Finset α) (F : Finset (α × α)), U ⊆ V ∧ U.Nonempty ∧
      θ ^ 2 * N / 16 ≤ (U.card : ℝ) ∧
      (∀ p ∈ F, R p.1 p.2 ∧ p.1 ∈ U ∧ p.2 ∈ U) ∧
      (∀ x, (F.filter (fun p => p.1 = x)).card = (F.filter (fun p => p.2 = x)).card) ∧
      ∀ S ⊆ U, θ ^ 3 / 64 * S.card * (U \ S).card ≤
        ((F.filter (fun p => p.1 ∈ S ∧ p.2 ∈ U \ S)).card : ℝ) := by sorry

end BinaryThreeLCC.JM
