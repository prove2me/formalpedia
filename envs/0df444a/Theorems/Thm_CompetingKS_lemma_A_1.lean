-- Prove2me | Theorems.Thm_CompetingKS_lemma_A_1
-- name    : CompetingKS.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:39.959182+00:00
-- url     : https://prove2.me/theorems/cb7eb19d-4ab9-467e-9330-10001d488896
-- title:
--   Lemma A.1 — maximum profits (20)–(21) of the one-to-two channel and the Pareto-dominated contracts
-- statement:
--   Consider the one-to-two channel with $a=b=1$, $c=0$, and let $\eta\in[0,1]$, $w_j\in[0,1]$. Put $w^d=\frac12+\frac12\sqrt{\frac{2-\eta}{2+\eta}}$. The maximum profits of the supplier and of retailer $i$ in unit $i$ are
--   $$
--   \overline\Pi_i(w_j)=\begin{cases}\Pi_i\bigl(\frac{2-\eta+2\eta w_j}4,w_j\bigr)=\frac{2-\eta}{8(2+\eta)}+\frac12w_j(1-w_j)&w_j<w^d,\\[2pt]\Pi_i\bigl(\frac12,w_j\bigr)=\frac18&w_j>w^d,\end{cases}
--   $$
--   $$
--   \overline\pi_i(w_j)=\begin{cases}\pi_i\bigl(\frac{\eta w_j}2,w_j\bigr)=\frac1{(2+\eta)^2}&w_j<\frac2{2+\eta},\\[2pt]\pi_i(1-w_j,w_j)=\frac{w_j^2}4&w_j>\frac2{2+\eta}.\end{cases}
--   $$
--   Moreover, the allocation of every contract $w_i\in[0,1]$ above the maximizer attaining $\overline\Pi_i(w_j)$ is Pareto-dominated.
--
--   These are the endpoints of the Kalai–Smorodinsky ratio in the one-to-two channel, and the Moreover clause locates the Pareto set.
--
--   Differences from the source:
--   - encoding: contracts wᵢ with no stated range in the appendix → contracts w ∈ [0, 1], and the printed strict ranges of wⱼ inside [0, 1]; reason: [c, a] is the paper's contract space (p.15), which normalizes to [0, 1]
--   - reading: "the maximum profits are" with Π̄ᵢ(wⱼ) = Πᵢ(x, wⱼ) → x attains the maximum in (9), resp. (10), and the supremum equals the printed value; reason: keeps the attained maximizers of the statement
--   - reading: "Pareto-dominated for wᵢ above the maximizer" → every contract w ∈ [0, 1] above the maximizer is dominated by some contract in [0, 1]; reason: the paper's Pareto notion, axiom (i), p.7
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, Lemma A.1, online appendix p.3

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- Lemma A.1, Feng, Li, Shanthikumar, *Negotiations in Competing Supply Chains: The
Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July 3, 2021),
SSRN 3447674, online appendix p.3: the maximum profits (20), (21) of the normalized one-to-two
channel, the contracts attaining them, and the Pareto domination of the contracts above the
maximizer of `Π̄ᵢ(wⱼ)`.

**Formalization Note** `wⱼ ∈ [0, 1]`, on the printed strict ranges. Attainment is `IsSMaximizer`,
`IsBMaximizer`; `Sbar`, `Bbar` are the suprema in (9), (10). The Moreover clause is stated for
contracts `w ∈ [0, 1]`. -/
theorem lemma_A_1 {η wj : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hwj : wj ∈ Set.Icc (0 : ℝ) 1) :
    (wj < 1 / 2 + 1 / 2 * √((2 - η) / (2 + η)) →
      (normOT η wj).IsSMaximizer ((2 - η + 2 * η * wj) / 4) ∧
      (normOT η wj).S ((2 - η + 2 * η * wj) / 4) =
        (2 - η) / (8 * (2 + η)) + 1 / 2 * wj * (1 - wj) ∧
      (normOT η wj).Sbar = (2 - η) / (8 * (2 + η)) + 1 / 2 * wj * (1 - wj) ∧
      ∀ w ∈ (normOT η wj).W, (2 - η + 2 * η * wj) / 4 < w → (normOT η wj).IsDominated w) ∧
    (1 / 2 + 1 / 2 * √((2 - η) / (2 + η)) < wj →
      (normOT η wj).IsSMaximizer (1 / 2) ∧
      (normOT η wj).S (1 / 2) = 1 / 8 ∧
      (normOT η wj).Sbar = 1 / 8 ∧
      ∀ w ∈ (normOT η wj).W, 1 / 2 < w → (normOT η wj).IsDominated w) ∧
    (wj < 2 / (2 + η) →
      (normOT η wj).IsBMaximizer (η * wj / 2) ∧
      (normOT η wj).B (η * wj / 2) = 1 / (2 + η) ^ 2 ∧
      (normOT η wj).Bbar = 1 / (2 + η) ^ 2) ∧
    (2 / (2 + η) < wj →
      (normOT η wj).IsBMaximizer (1 - wj) ∧
      (normOT η wj).B (1 - wj) = wj ^ 2 / 4 ∧
      (normOT η wj).Bbar = wj ^ 2 / 4) := by sorry

end CompetingKS
