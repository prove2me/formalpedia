-- Prove2me | Theorems.Thm_AutomaticSelfReduction_Lifting_lemma_5_4
-- name    : AutomaticSelfReduction.Lifting.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:42.093566+00:00
-- url     : https://prove2.me/theorems/8d57f1a1-b7e1-40f8-bf16-fb2109e6e644
-- title:
--   Lemma 5.4 — the discrepancy of the faster algorithm is at most 16(b+1) times the node error
-- statement:
--   Let $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$ be a normalized 2-separated $b$-dominant problem. Let $p_1,\dots,p_\delta$ be probability vectors on $\Sigma$ and let $X=(X_1,\dots,X_\delta)$ have independent coordinates $X_i\sim p_i$. With $\varepsilon_v=\mathbb E[d(X,C_B)]$ and $d_v=\min_C D(C)$ over valid tuples $C$ (where $D(C)=\sum_i(1-p_{i,C_i})$),
--   $$
--   d_v\le 16(b+1)\,\varepsilon_v .
--   $$
--
--   In the paper $p_i$ is the conditional law of the given algorithm's output on port $i$ of a black node $v$ given its $(T-1)$-neighbourhood; the bound, summed over black nodes, gives the factor $16(1+b)$ of Lemma 5.2. The constant depends on the dominance parameter $b$ but not on the degree $\delta$.
--
--   **Formalization Note** The minimum is over all ordered tuples whose multiset lies in $C_B$; it is attained, the set being finite and nonempty.
--
--   Differences from the source:
--   - generalization: p_{i,ℓ} = Pr[A outputs ℓ on port i of the black node v | B_{T−1}(v)], independent across ports by the girth assumption → an arbitrary family of probability vectors p_1, …, p_δ with the product law; reason: the proof uses only the product law; the conditional marginals of A are such a family
--   - encoding: d_v = D(C_v) for the output C_v of A' → the minimum of D over valid tuples; reason: A' outputs a valid tuple of minimum discrepancy
--   - encoding: ε_v = E[d(X, C_B)] with d the number of differing positions between ordered tuples, C_B seen as a set of tuples → Σ_Z Pr[Z]·d(m(Z), C_B) with the multiset distance of Definition 2.5–2.6 applied to the multiset m(Z) of the tuple Z; reason: the Hamming distance from a tuple to the permutation-closed set of valid tuples equals the multiset distance, so the two values coincide
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Lemma 5.4, printed p. 15 (PDF p. 16); definitions of p_{i,ℓ}, D, ε_v, d_v on printed pp. 13–14; proof printed pp. 15–20

import Definitions.Def_AutomaticSelfReduction_Lifting_Discrepancy

namespace AutomaticSelfReduction.Lifting

/-- Lemma 5.4 (Balliu–d'Amore–Olivetti, STOC 2027 submission #338, PDF p. 16, printed p. 15),
`d_v ≤ 16(b + 1) ε_v`, stated for arbitrary independent port laws `p₁, …, p_δ`: for a normalized
2-separated `b`-dominant problem, the minimum discrepancy of a valid black tuple is at most
`16(b + 1)` times the expected black error of a tuple with independent coordinates `Xᵢ ∼ pᵢ`. -/
theorem lemma_5_4 {L : Type*} [Fintype L] [DecidableEq L] {Δ δ : ℕ} (P : Problem L Δ δ)
    (hN : P.IsNormalized) (h2 : P.TwoSeparated) (b : ℕ) (hb : P.Dominant b)
    (p : Fin δ → L → ℝ) (hp : IsProbVectors p) :
    minDisc p P.CB ≤ 16 * ((b : ℝ) + 1) * nodeError p P.CB := by sorry

end AutomaticSelfReduction.Lifting
