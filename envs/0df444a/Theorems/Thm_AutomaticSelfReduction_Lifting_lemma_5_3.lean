-- Prove2me | Theorems.Thm_AutomaticSelfReduction_Lifting_lemma_5_3
-- name    : AutomaticSelfReduction.Lifting.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:32.366087+00:00
-- url     : https://prove2.me/theorems/f710a981-d6bd-4912-9a85-b473904fbd90
-- title:
--   Lemma 5.3 — the discrepancy of the faster algorithm is at most 2δ times the node error
-- statement:
--   Let $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$ be a normalized 2-separated problem. Let $p_1,\dots,p_\delta$ be probability vectors on $\Sigma$ and let $X$ have independent coordinates $X_i\sim p_i$. With $\varepsilon_v=\mathbb E[d(X,C_B)]$ and $d_v=\min_C D(C)$ over valid tuples $C$,
--   $$
--   d_v\le 2\delta\,\varepsilon_v .
--   $$
--
--   This degree-dependent bound uses only 2-separation; Lemma 5.4 applies it when $\delta<8(b+1)$ and otherwise replaces the factor $2\delta$ by $16(b+1)$.
--
--   Differences from the source:
--   - generalization: p_{i,ℓ} = Pr[A outputs ℓ on port i of the black node v | B_{T−1}(v)], independent across ports by the girth assumption → an arbitrary family of probability vectors p_1, …, p_δ with the product law; reason: the proof uses only the product law; the conditional marginals of A are such a family
--   - generalization: the ambient problem of §5 is also b-dominant → b-dominance not assumed; reason: §5.2 states that this bound only exploits 2-separation; the source's problem satisfies the weaker hypotheses
--   - encoding: d_v = D(C_v) for the output C_v of A' → the minimum of D over valid tuples; reason: A' outputs a valid tuple of minimum discrepancy
--   - encoding: ε_v = E[d(X, C_B)] with d the number of differing positions between ordered tuples, C_B seen as a set of tuples → Σ_Z Pr[Z]·d(m(Z), C_B) with the multiset distance of Definition 2.5–2.6 applied to the multiset m(Z) of the tuple Z; reason: the Hamming distance from a tuple to the permutation-closed set of valid tuples equals the multiset distance, so the two values coincide
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Lemma 5.3, printed p. 14 (PDF p. 15); definitions of ε_v, d_v on printed p. 14

import Definitions.Def_AutomaticSelfReduction_Lifting_Discrepancy

namespace AutomaticSelfReduction.Lifting

/-- Lemma 5.3 (Balliu–d'Amore–Olivetti, STOC 2027 submission #338, PDF p. 15, printed p. 14),
`d_v ≤ 2δ ε_v`, stated for arbitrary independent port laws `p₁, …, p_δ`: for a normalized
2-separated problem, the minimum discrepancy of a valid black tuple is at most `2δ` times the
expected black error `E[d(X, C_B)]` of a tuple `X` with independent coordinates `Xᵢ ∼ pᵢ`. -/
theorem lemma_5_3 {L : Type*} [Fintype L] [DecidableEq L] {Δ δ : ℕ} (P : Problem L Δ δ)
    (hN : P.IsNormalized) (h2 : P.TwoSeparated) (p : Fin δ → L → ℝ) (hp : IsProbVectors p) :
    minDisc p P.CB ≤ 2 * (δ : ℝ) * nodeError p P.CB := by sorry

end AutomaticSelfReduction.Lifting
