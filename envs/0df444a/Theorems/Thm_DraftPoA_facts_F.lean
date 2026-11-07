-- Prove2me | Theorems.Thm_DraftPoA_facts_F
-- name    : DraftPoA.facts_F
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:57.856227+00:00
-- url     : https://prove2.me/theorems/97cefcd6-2916-4e06-9021-b56de082ef41
-- title:
--   (F1)–(F3): $q(S)>\sigma_j$, $h<\sigma_N\le\sigma_{t_{\min}}$, and display (3)
-- statement:
--   Let $N\ge4$, let $S\subseteq\{1,\dots,N\}$ be nonempty, $t_{\min}=\min S$, $q(S)=\varphi_{t_{\min}}$, $K=\lceil H_N\rceil$ and $\delta=\delta_N$.
--
--   1. **(F1)** $q(S)>\sigma_j$ for every $j\in S$.
--   2. **(F2)** $h<\sigma_N\le\sigma_{t_{\min}}$.
--   3. **(F3)** For every bid $\beta\ge\sigma_{t_{\min}}$,
--
--   $$\sum_{j\in S:\,\alpha_j>\beta}(\alpha_j-\beta)\ \le\ \sum_{j=t_{\min}}^{t_{\min}K-1}\frac1j+\delta\ \le\ \frac1{t_{\min}}+\int_{t_{\min}}^{t_{\min}K}\frac{dy}{y}+\delta\ =\ \frac1{t_{\min}}+\ln K+\delta\ \le\ 1+\ln K+\delta.$$
--
--   (F1) makes the threat outbid the sink bidders, (F2) makes rent items unprofitable at any winning bid, and (F3) bounds what $A$ gains in a round won at a single price.
--
--   **Formalization Note** $\beta$ ranges over all reals, which Remark B.7 (i) needs.
--
--   Differences from the source:
--   - generalization: every bid β ≥ σ_{t_min} → every real β ≥ σ_{t_min}; reason: the argument uses only β ≥ σ_{t_min}; grid bids are a special case
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), (F1)–(F3) and display (3), App. B, pp.21–22 (PDF 22–23)

import Mathlib
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Facts (F1)–(F3) and display (3), App. B, pp.21–22 (PDF 22–23) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

Let `N ≥ 4` and let `S ⊆ {1, …, N}` be a nonempty set of unsold sink items, `t_min = min S`,
`q(S) = φ_{t_min}`. (F1) `q(S) > σ_j` for every `j ∈ S`. (F2) `h < σ_N ≤ σ_{t_min}`. (F3) for every
bid `β ≥ σ_{t_min}`,
`Σ_{j∈S: α_j>β} (α_j − β) ≤ Σ_{j=t_min}^{t_min K−1} 1/j + δ ≤ 1/t_min + ∫_{t_min}^{t_min K} dy/y + δ
= 1/t_min + ln K + δ ≤ 1 + ln K + δ`.

**Formalization Note.** Sink items are numbered `1, …, N` here (natural numbers). `β` is any real
number, not only a grid price. `δ` is the value-rounding increment `δ_N`. -/
theorem facts_F (N : ℕ) (hN : 4 ≤ N) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
    (hne : S.Nonempty) :
    let t := S.min' hne
    (∀ j ∈ S, sigma N j < phi N t) ∧
    (hOf N < sigma N N ∧ sigma N N ≤ sigma N t) ∧
    (∀ β : ℝ, sigma N t ≤ β →
      ∑ j ∈ S.filter (fun j => β < alpha N j), (alpha N j - β) ≤
          ∑ j ∈ Finset.Ico t (t * Kof N), 1 / (j : ℝ) + deltaOf N ∧
      ∑ j ∈ Finset.Ico t (t * Kof N), 1 / (j : ℝ) + deltaOf N ≤
          1 / (t : ℝ) + (∫ y in (t : ℝ)..((t : ℝ) * Kof N), 1 / y) + deltaOf N ∧
      (∫ y in (t : ℝ)..((t : ℝ) * Kof N), 1 / y) = Real.log (Kof N) ∧
      1 / (t : ℝ) + Real.log (Kof N) + deltaOf N ≤ 1 + Real.log (Kof N) + deltaOf N) := by sorry

end DraftPoA
