-- Prove2me | Theorems.Thm_FirstPriceLearning_Stochastic_lemma_2
-- name    : FirstPriceLearning.Stochastic.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:56.347463+00:00
-- url     : https://prove2.me/theorems/3d1eb9ec-a68b-48f1-958a-d17e046b1cb6
-- title:
--   Lemma 2, p. 18 — in Algorithm 3, N^{t−1}_{c_t} ≥ (∑_{s<t} 𝟙(c_s ⪯ c_t))/(α log(MKT²/δ)) − 1 w.p. ≥ 1 − δ
-- statement:
--   Consider a partially ordered contextual bandit (Definition 3) with $M,K\ge1$ whose feedback graph has independence number at most $\alpha$, run Algorithm 3 with a topological ordering of the contexts and failure probability $\delta\in(0,1)$, and fix any context sequence $c_1,\dots,c_T$ ($T\ge1$). Let $N^{t}_c$ be the minimum count of context $c$ at the end of round $t$. Then with probability at least $1-\delta$, for every $t\in[T]$,
--
--   $$
--   N^{t-1}_{c_t}\ \ge\ \frac{\sum_{s<t}\mathbb 1(c_s\preceq_{\mathcal C}c_t)}{\alpha\log(MKT^2/\delta)}-1 .
--   $$
--
--   Choosing an action under a small context reveals rewards useful under every larger context; the lemma quantifies how fast the minimum counts of large contexts grow.
--
--   **Formalization Note.** The probability is over the iid reward vectors and the uniform choices of the algorithm, for every fixed context sequence (the proof fixes the contexts); this covers random contexts independent of the rest. A minimum count equal to $+\infty$ (an empty active set) satisfies every lower bound. "With probability at least $1-\delta$" is stated as: the (outer) measure of the failure set is at most $\delta$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 18, Lemma 2 (proof: App. C.2, p. 39)

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Algorithm3

namespace FirstPriceLearning.Stochastic

open MeasureTheory

open scoped Classical in
/-- Lemma 2 (p. 18): run Algorithm 3 with failure probability `δ ∈ (0, 1)` on a partially ordered
contextual bandit (Definition 3) whose feedback graph has independence number at most `α`, on any
fixed context sequence `c_1, …, c_T`. With probability at least `1 - δ` (over the iid reward
vectors and the algorithm's uniform choices), for every round `t ∈ [T]`,
`N^{t-1}_{c_t} ≥ (∑_{s<t} 𝟙(c_s ⪯_𝒞 c_t)) / (α log(MKT²/δ)) - 1`. (A minimum count equal to `⊤`,
which only arises from an empty active set, satisfies every lower bound.) -/
theorem lemma_2 (M K T : ℕ) (hM : 0 < M) (hK : 0 < K) (hT : 1 ≤ T) (B : ContextualBandit M K)
    (leC : Fin M → Fin M → Prop) (hB : IsPartiallyOrdered B leC) (α : ℕ)
    (hα : IndepNumberLe B.E α) (ord : Fin M ≃ Fin M) (hord : IsTopoOrder leC ord) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (cs : Fin T → Fin M) :
    let p : Alg3Params M K := ⟨T, δ, B.E, leC, ord, hK⟩
    ((Measure.pi fun _ : Fin T => B.P).prod (Measure.pi fun _ : Fin T => (volume : Measure unitInterval)))
      {ω | ¬ ∀ t : Fin T,
        (Alg3.state p cs ω.1 ω.2 t.val).Nmin (cs t) = ⊤ ∨
          ((Finset.univ.filter (fun s : Fin T => s < t ∧ leC (cs s) (cs t))).card : ℝ) /
              (α * Real.log (M * K * (T : ℝ) ^ 2 / δ)) - 1 ≤
            (((Alg3.state p cs ω.1 ω.2 t.val).Nmin (cs t)).toNat : ℝ)} ≤
      ENNReal.ofReal δ := by sorry

end FirstPriceLearning.Stochastic
