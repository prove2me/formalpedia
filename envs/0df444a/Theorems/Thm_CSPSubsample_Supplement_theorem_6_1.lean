-- Prove2me | Theorems.Thm_CSPSubsample_Supplement_theorem_6_1
-- name    : CSPSubsample.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:54:43.294214+00:00
-- url     : https://prove2.me/theorems/589e0f72-9d5f-42be-a9f5-0e7ded6c040f
-- title:
--   Theorem 6.1 (Subsampling of $k$-Player Free Games): $\mathbb E_S[\omega(G_S)]\le\omega(G)+O(\varepsilon)$ for $N=c\,k^{12}\varepsilon^{-6}\log^2(k^2|B_1|\cdots|B_k|/\varepsilon)$
-- statement:
--   There is an absolute constant $c>0$ (and an absolute constant $C>0$ in the $O(\varepsilon)$) such that the following holds. Let $\varepsilon>0$ and let $G=((Y_i),(B_i),V)$ be a $k$-player free game with
--   $$
--   |Y_1|\cdots|Y_k|\ \ge\ c^2\,\frac{k^{24}}{\varepsilon^{13}}\,\log^4\!\Big(\frac{k^2|B_1|\cdots|B_k|}{\varepsilon}\Big),
--   \qquad
--   N:=\Big\lceil c\,\frac{k^{12}}{\varepsilon^{6}}\,\log^2\!\Big(\frac{k^2|B_1|\cdots|B_k|}{\varepsilon}\Big)\Big\rceil.
--   $$
--   For each player $i\in[k]$ choose a tuple $S_i$ of size $N$ by sampling elements of $Y_i$ uniformly at random with replacement, let $S=S_1\times\cdots\times S_k$, and let $G_S$ be the subgame of $G$ in which the questions of the $i$-th player are sampled uniformly from $S_i$. Then
--   $$
--   \mathbb E_S\big[\omega(G_S)\big]\ \le\ \omega(G)+C\varepsilon .
--   $$
--
--   Restricting each prover to $N$ sampled questions, with $N$ polynomial in $k$ and $1/\varepsilon$ and polylogarithmic in the answer sets, does not increase the value of a free game by more than $O(\varepsilon)$ on average. By Aaronson, Impagliazzo and Moshkovitz (Theorem 53 of their paper), this is the ingredient that reduces AM(poly) to AM.
--
--   **Formalization Note** $\omega(G)$ is `FreeGame.value`, $\omega(G_S)$ is `FreeGame.subgameValue` and $\mathbb E_S$ is `FreeGame.expSubgameValue`. The constants $c$ and $C$ are chosen before $k$, $\varepsilon$ and the game; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: N := c k¹²/ε⁶ log²(k²|B_1|⋯|B_k|/ε), a real number → the natural number ⌈c k¹²/ε⁶ log²(k²|B_1|⋯|B_k|/ε)⌉₊; reason: a tuple size must be a natural number; the same reading as the published Theorem 3.3 of this mission.
--   - encoding: O(ε) → an explicit constant C > 0 chosen with c before k, ε and G; reason: the paper's O(ε) hides an absolute constant (its proof bounds k²/N and (N² + k²)/|Y| by absolute multiples of ε).
--   - encoding: log without a base → Real.log; reason: a change of base rescales c, which is existentially quantified.
--   - encoding: finite question and answer sets → finite and nonempty; reason: the uniform question y_i ∼ Y_i and the maximum over b_i : Y_i → B_i are undefined for empty sets, so no instance of the source is excluded.
--   - reading: G_S, the questions of player i "uniformly sampled from S_i" → the position j ∈ [N] uniform, so a repeated element counts with its multiplicity, strategies b_i a function of the question (b_i : Y_i → B_i, only its values on S_i used); reason: the proof compares the question law with ⊗_i Unif(S_i) for the tuple S_i (pp. 24–25) and footnote 2 (p. 24) requires equal elements to get equal answers.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Theorem 6.1 (Subsampling of k-Player Free Games), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_CSPSubsample_Supplement_FreeGame
import Definitions.Def_CSPSubsample_Supplement_subgameValue

set_option autoImplicit false

namespace CSPSubsample.Supplement

/-- **Theorem 6.1 (Subsampling of k-Player Free Games)** (arXiv:2608.00203 (PDF sha256
fd9ae011…), p.23 = PDF p.25). There exists a constant `c > 0` such that for any `ε > 0` and any
`k`-player free game `G` with `|Y_1|⋯|Y_k| ≥ c² k²⁴/ε¹³ log⁴(k²|B_1|⋯|B_k|/ε)`, letting
`N := c k¹²/ε⁶ log²(k²|B_1|⋯|B_k|/ε)`, choosing for each `i ∈ [k]` a tuple `S_i` of size `N` by
sampling elements uniformly with replacement from `Y_i`, and letting `G_S` be the subgame where
the questions of the `i`-th player are uniformly sampled from `S_i`, `E_S[ω(G_S)] ≤ ω(G) + O(ε)`.

**Formalization Note** `c` and the `O(ε)` constant `C` are absolute: both are chosen before
`k`, `ε` and the game. `N` is the natural number `⌈c k¹²ε⁻⁶ log²(k²|B_1|⋯|B_k|/ε)⌉₊`; `log` is
`Real.log`. The same `c` appears in the size hypothesis and in `N`. `E_S` is the average over
`S ∈ ∏_i Y_i^N` (`expSubgameValue`), `ω(G_S)` is `subgameValue` (questions uniform over the `N`
positions of each `S_i`), `ω(G)` is `value`. -/
theorem theorem_6_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ G : FreeGame k,
      c ^ 2 * (k : ℝ) ^ 24 / ε ^ 13 *
          Real.log ((k : ℝ) ^ 2 * (∏ i, (Fintype.card (G.B i) : ℝ)) / ε) ^ 4 ≤
        ∏ i, (Fintype.card (G.Y i) : ℝ) →
      G.expSubgameValue
          ⌈c * (k : ℝ) ^ 12 / ε ^ 6 *
            Real.log ((k : ℝ) ^ 2 * (∏ i, (Fintype.card (G.B i) : ℝ)) / ε) ^ 2⌉₊ ≤
        G.value + C * ε := by sorry

end CSPSubsample.Supplement
