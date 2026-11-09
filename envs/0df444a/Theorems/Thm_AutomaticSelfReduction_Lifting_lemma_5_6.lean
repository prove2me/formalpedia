-- Prove2me | Theorems.Thm_AutomaticSelfReduction_Lifting_lemma_5_6
-- name    : AutomaticSelfReduction.Lifting.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:21.838078+00:00
-- url     : https://prove2.me/theorems/a0d404a5-67c1-4780-93f4-84eaf99124bf
-- title:
--   Lemma 5.6 — restricted discrepancy bound for configurations dominated by ℓ*
-- statement:
--   Let $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$ be a normalized 2-separated problem, let $b\ge0$ be an integer and $\ell^*\in\Sigma$ a label. Let $p_1,\dots,p_\delta$ be probability vectors on $\Sigma$ and $X$ have independent coordinates $X_i\sim p_i$. Put
--   $$
--   C_{\ell^*}=\{C\in C_B:m_C(\ell^*)\ge\delta-b\},\qquad q_{\ell^*}=\Pr[X\notin C_{\ell^*}],\qquad d_{\ell^*}=\min_{C\in C_{\ell^*}}D(C),
--   $$
--   with $C_{\ell^*}$ read as a set of ordered tuples and $D_{\ell^*}=\sum_i(1-p_{i,\ell^*})$. If $q_{\ell^*}<1$, then
--   $$
--   d_{\ell^*}\le\frac{(D_{\ell^*}+b+1)\,q_{\ell^*}}{1-q_{\ell^*}} .
--   $$
--
--   It is the analogue of Lemma 5.3 when only the configurations dominated by $\ell^*$ are allowed; in the proof of Lemma 5.4 it is applied to the label $\ell^*$ of Lemma 5.5.
--
--   **Formalization Note** $q_{\ell^*}<1$ forces $C_{\ell^*}$ to be nonempty, so the minimum is attained.
--
--   Differences from the source:
--   - generalization: p_{i,ℓ} = Pr[A outputs ℓ on port i of the black node v | B_{T−1}(v)], independent across ports by the girth assumption → an arbitrary family of probability vectors p_1, …, p_δ with the product law; reason: the proof uses only the product law; the conditional marginals of A are such a family
--   - generalization: ℓ* the label of Lemma 5.5, inside the case δ ≥ 8(b+1), ℓ* ∈ D, ε_v < 1/4, for a b-dominant Π → every label ℓ* and every b, with neither the case assumptions nor b-dominance; reason: the proof uses only 2-separation, the product law and q_{ℓ*} < 1; the source's instance satisfies these hypotheses
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Lemma 5.6, printed p. 17 (PDF p. 18); C_ℓ*, q_ℓ*, d_ℓ* defined on printed p. 17; proof printed pp. 17–19

import Definitions.Def_AutomaticSelfReduction_Lifting_Discrepancy

namespace AutomaticSelfReduction.Lifting

/-- Lemma 5.6 (Balliu–d'Amore–Olivetti, STOC 2027 submission #338, PDF p. 18, printed p. 17),
stated for arbitrary independent port laws `p₁, …, p_δ`, every `b` and every label `ℓ*`: for a
normalized 2-separated problem, if `q_{ℓ*} = Pr[X ∉ C_{ℓ*}] < 1` then
`d_{ℓ*} ≤ (D_{ℓ*} + b + 1) q_{ℓ*} / (1 − q_{ℓ*})`, where
`C_{ℓ*} = {C ∈ C_B : m_C(ℓ*) ≥ δ − b}` and `d_{ℓ*} = min_{C ∈ C_{ℓ*}} D(C)`. -/
theorem lemma_5_6 {L : Type*} [Fintype L] [DecidableEq L] {Δ δ : ℕ} (P : Problem L Δ δ)
    (hN : P.IsNormalized) (h2 : P.TwoSeparated) (b : ℕ) (ℓ : L)
    (p : Fin δ → L → ℝ) (hp : IsProbVectors p)
    (hq : restrictedFailure p P.CB b ℓ < 1) :
    restrictedMinDisc p P.CB b ℓ ≤
      (constDisc p ℓ + b + 1) * restrictedFailure p P.CB b ℓ /
        (1 - restrictedFailure p P.CB b ℓ) := by sorry

end AutomaticSelfReduction.Lifting
