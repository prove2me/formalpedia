-- Prove2me | Theorems.Thm_CompetingKS_lemma_A_4
-- name    : CompetingKS.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:48.389077+00:00
-- url     : https://prove2.me/theorems/42942e2b-b0a7-456b-ac45-462fb57c6760
-- title:
--   Lemma A.4 — maximum profits (38)–(39) of the two-to-one channel and the Pareto-dominated contracts
-- statement:
--   Consider the two-to-one channel with $a=b=1$, $c=0$, and let $\eta\in[0,1)$, $w_j\in[0,1]$. The maximum profits of supplier $i$ and of the retailer in unit $i$ are
--   $$
--   \overline\Pi_i(w_j)=\begin{cases}\Pi_i\bigl(\frac{1-\eta+\eta w_j}2,w_j\bigr)=\frac{(1-\eta(1-w_j))^2}{8(1-\eta^2)}&w_j<\frac{(2+\eta)(1-\eta)}{2-\eta^2},\\[2pt]\Pi_i\bigl(\frac{w_j-1+\eta}\eta,w_j\bigr)=\frac{(1-w_j)(w_j-1+\eta)}{2\eta^2}&\frac{(2+\eta)(1-\eta)}{2-\eta^2}<w_j<\frac{2-\eta}2,\\[2pt]\Pi_i\bigl(\frac12,w_j\bigr)=\frac18&w_j>\frac{2-\eta}2,\end{cases}
--   $$
--   $$
--   \overline\pi_i(w_j)=\begin{cases}\pi_i(0,w_j)=\frac{(1-w_j)^2-2\eta(1-w_j)+1}{4(1-\eta^2)}&w_j<1-\eta,\\[2pt]\pi_i(0,w_j)=\frac14&w_j>1-\eta.\end{cases}
--   $$
--   Moreover, the allocation of every contract $w_i\in[0,1]$ above the maximizer attaining $\overline\Pi_i(w_j)$ is Pareto-dominated.
--
--   These are the endpoints of the Kalai–Smorodinsky ratio in the two-to-one channel, and the Moreover clause locates the Pareto set.
--
--   **Formalization Note** The middle range of the first display is empty at $\eta=0$.
--
--   Differences from the source:
--   - encoding: contracts wᵢ with no stated range in the appendix → contracts w ∈ [0, 1], and the printed strict ranges of wⱼ inside [0, 1]; reason: [c, a] is the paper's contract space (p.15), which normalizes to [0, 1]
--   - encoding: η ∈ [0, 1] for the two-to-one channel → η ∈ [0, 1); reason: at η = 1, wᵢ = wⱼ < a Lemma 1(ii)(a) gives q*ᵢ = 0 and (ii)(c) gives q*ᵢ = (a − wᵢ)/(2b), and (ii)(b) divides by 1 − η² = 0, so q* and the profits are undefined there; this excludes only that undefined case
--   - reading: "the maximum profits are" with Π̄ᵢ(wⱼ) = Πᵢ(x, wⱼ) → x attains the maximum in (9), resp. (10), and the supremum equals the printed value; reason: keeps the attained maximizers of the statement
--   - reading: "Pareto-dominated for wᵢ above the maximizer" → every contract w ∈ [0, 1] above the maximizer is dominated by some contract in [0, 1]; reason: the paper's Pareto notion, axiom (i), p.7
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, Lemma A.4, online appendix p.9

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- Lemma A.4, Feng, Li, Shanthikumar, *Negotiations in Competing Supply Chains: The
Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July 3, 2021),
SSRN 3447674, online appendix p.9: the maximum profits (38), (39) of the normalized two-to-one
channel, the contracts attaining them, and the Pareto domination of the contracts above the
maximizer of `Π̄ᵢ(wⱼ)`.

**Formalization Note** `η ∈ [0, 1)`, `wⱼ ∈ [0, 1]`, on the printed strict ranges. The middle range
of (38) is empty at `η = 0`, so its division by `η` is harmless. Attainment is `IsSMaximizer`,
`IsBMaximizer`; `Sbar`, `Bbar` are the suprema in (9), (10). -/
theorem lemma_A_4 {η wj : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) (hwj : wj ∈ Set.Icc (0 : ℝ) 1) :
    (wj < (2 + η) * (1 - η) / (2 - η ^ 2) →
      (normTO η wj).IsSMaximizer ((1 - η + η * wj) / 2) ∧
      (normTO η wj).S ((1 - η + η * wj) / 2) = (1 - η * (1 - wj)) ^ 2 / (8 * (1 - η ^ 2)) ∧
      (normTO η wj).Sbar = (1 - η * (1 - wj)) ^ 2 / (8 * (1 - η ^ 2)) ∧
      ∀ w ∈ (normTO η wj).W, (1 - η + η * wj) / 2 < w → (normTO η wj).IsDominated w) ∧
    ((2 + η) * (1 - η) / (2 - η ^ 2) < wj → wj < (2 - η) / 2 →
      (normTO η wj).IsSMaximizer ((wj - 1 + η) / η) ∧
      (normTO η wj).S ((wj - 1 + η) / η) = (1 - wj) * (wj - 1 + η) / (2 * η ^ 2) ∧
      (normTO η wj).Sbar = (1 - wj) * (wj - 1 + η) / (2 * η ^ 2) ∧
      ∀ w ∈ (normTO η wj).W, (wj - 1 + η) / η < w → (normTO η wj).IsDominated w) ∧
    ((2 - η) / 2 < wj →
      (normTO η wj).IsSMaximizer (1 / 2) ∧
      (normTO η wj).S (1 / 2) = 1 / 8 ∧
      (normTO η wj).Sbar = 1 / 8 ∧
      ∀ w ∈ (normTO η wj).W, 1 / 2 < w → (normTO η wj).IsDominated w) ∧
    (wj < 1 - η →
      (normTO η wj).IsBMaximizer 0 ∧
      (normTO η wj).B 0 = ((1 - wj) ^ 2 - 2 * η * (1 - wj) + 1) / (4 * (1 - η ^ 2)) ∧
      (normTO η wj).Bbar = ((1 - wj) ^ 2 - 2 * η * (1 - wj) + 1) / (4 * (1 - η ^ 2))) ∧
    (1 - η < wj →
      (normTO η wj).IsBMaximizer 0 ∧
      (normTO η wj).B 0 = 1 / 4 ∧
      (normTO η wj).Bbar = 1 / 4) := by sorry

end CompetingKS
