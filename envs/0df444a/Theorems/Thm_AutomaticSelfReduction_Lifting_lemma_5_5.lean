-- Prove2me | Theorems.Thm_AutomaticSelfReduction_Lifting_lemma_5_5
-- name    : AutomaticSelfReduction.Lifting.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:38.364333+00:00
-- url     : https://prove2.me/theorems/753eccf2-af14-41d7-a243-6280d5cba9cf
-- title:
--   Lemma 5.5 — some constant tuple has discrepancy at most 2(ε_v+b)+1
-- statement:
--   Let $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$ be a normalized $b$-dominant problem. Let $p_1,\dots,p_\delta$ be probability vectors on $\Sigma$, let $X$ have independent coordinates $X_i\sim p_i$, and let $\varepsilon_v=\mathbb E[d(X,C_B)]$. Then there exists a label $\ell^*\in\Sigma$ with
--   $$
--   D_{\ell^*}=\sum_{i=1}^{\delta}\bigl(1-p_{i,\ell^*}\bigr)\le 2(\varepsilon_v+b)+1 .
--   $$
--
--   So the output at a node is, in expectation, close to a monochromatic configuration $(\ell^*,\dots,\ell^*)$; the label $\ell^*$ need not be dominant and the constant tuple need not be valid. This is the first step of the proof of Lemma 5.4.
--
--   Differences from the source:
--   - generalization: p_{i,ℓ} = Pr[A outputs ℓ on port i of the black node v | B_{T−1}(v)], independent across ports by the girth assumption → an arbitrary family of probability vectors p_1, …, p_δ with the product law; reason: the proof uses only the product law; the conditional marginals of A are such a family
--   - generalization: Π 2-separated (context of §5) → 2-separation not assumed; reason: the proof uses only b-dominance and the product law; the source's problem satisfies the weaker hypotheses
--   - encoding: ε_v = E[d(X, C_B)] with d the number of differing positions between ordered tuples, C_B seen as a set of tuples → Σ_Z Pr[Z]·d(m(Z), C_B) with the multiset distance of Definition 2.5–2.6 applied to the multiset m(Z) of the tuple Z; reason: the Hamming distance from a tuple to the permutation-closed set of valid tuples equals the multiset distance, so the two values coincide
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Lemma 5.5, printed p. 16 (PDF p. 17); D_ℓ defined on printed p. 16

import Definitions.Def_AutomaticSelfReduction_Lifting_Discrepancy

namespace AutomaticSelfReduction.Lifting

/-- Lemma 5.5 (Balliu–d'Amore–Olivetti, STOC 2027 submission #338, PDF p. 17, printed p. 16),
stated for arbitrary independent port laws `p₁, …, p_δ`: for a normalized `b`-dominant problem
there exists a label `ℓ*` with `D_{ℓ*} ≤ 2(ε_v + b) + 1`. -/
theorem lemma_5_5 {L : Type*} [Fintype L] [DecidableEq L] {Δ δ : ℕ} (P : Problem L Δ δ)
    (hN : P.IsNormalized) (b : ℕ) (hb : P.Dominant b)
    (p : Fin δ → L → ℝ) (hp : IsProbVectors p) :
    ∃ ℓ : L, constDisc p ℓ ≤ 2 * (nodeError p P.CB + b) + 1 := by sorry

end AutomaticSelfReduction.Lifting
