-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_card_fProd_le
-- name    : ErschlerZheng.not_forall_card_fProd_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:02.960995+00:00
-- url     : https://prove2.me/theorems/f065b48f-f15d-4acc-b21b-b10cf28ae48b
-- title:
--   Lemma 7.17 (ii) without n ⩾ 1 fails — for some D, ω and (k_n) meeting the lemma's hypotheses, the bound fails for some n divisible by D
-- statement:
--   It is not true that for every $D$, every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), every sequence $(k_n)$ satisfying the standing assumption of p. 40 (`IsAdmissibleSeq`) and every $n$ divisible by $D$, part (ii) of Lemma 7.17 holds: that for every $\boldsymbol\epsilon \in \{0, 1\}^n$, every $\ell$ with $n \le \ell \le n + 2k_n + 2D + 5$ and every ray $x$ in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`), the proportion of $\boldsymbol\gamma \in \mathfrak F_n$ (`fProd`) with $d_{\mathcal S}(x, x \cdot \gamma_n^{\epsilon_n} \cdots \gamma_1^{\epsilon_1}) \ge k_n 2^\ell$ (`schreierDist`, `theta`) is at most $8k_n 2^{-(\ell - n)/D}$.
--
--   This is not a result of the paper. It shows that the hypothesis $n \ge 1$ of the milestone `ErschlerZheng.mass_uniformMeasure_fSet_le_and_card_fProd_le` cannot be dropped from part (ii). It backs the sentence of the note `mass_uniformMeasure_fSet_le_and_card_fProd_le` “at $n = 0$ with $k_0 = 0$ part (ii) fails at $\ell = 0$, where its left side is $1$ and its right side $0$”. The statement is part (ii) of that milestone, verbatim, with the hypothesis $n \ge 1$ removed.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 45, Lemma 7.17 (ii) without n ⩾ 1 (fails at n = 0)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

open scoped RightActions

namespace ErschlerZheng

theorem not_forall_card_fProd_le :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      ∀ n : ℕ, D ∣ n →
      ∀ ε : Fin n → Bool, ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ n + 2 * k n + 2 * D + 5 → ∀ x ∈ orbitOne ω,
        (Nat.card {γ : fProd D ω k n // k n * 2 ^ ℓ ≤ schreierDist ω x (x <• theta D ω k n (ε, γ))} :
            ℝ) / Nat.card (fProd D ω k n) ≤
          8 * k n * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by
  sorry

end ErschlerZheng
