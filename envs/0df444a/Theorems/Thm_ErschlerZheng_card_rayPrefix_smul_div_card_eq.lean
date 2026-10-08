-- Prove2me | Theorems.Thm_ErschlerZheng_card_rayPrefix_smul_div_card_eq
-- name    : ErschlerZheng.card_rayPrefix_smul_div_card_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T08:14:25.187513+00:00
-- url     : https://prove2.me/theorems/59b876b4-d447-4268-a9ec-bed59f79c8f0
-- title:
--   pp. 55–56, corrected — for x uniform on B_j and (ε, γ) on Λ_n, the first n digits of x·γ_{j+1}^{−ε_{j+1}}⋯γ_n^{−ε_n} are uniform on half of {0,1}^n; for g_j^{−1}, the first j − 1 digits, both orders
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), let $D$ divide $n$, and let $1 \le j \le n - k_n$ (written $j + k_n \le n$) with $\omega_{j-1} = \mathbf 2$. Let $B_j$ be the set of points $x$ of the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) at which the germ of $g_j$ (`seqG`) is not in $\mathcal H^b$ (`letterGerms ω .b`), and $B'_j$ the same set for $g_j^{-1}$. Then $B_j$, $B'_j$ and $\Lambda_n$ (`LambdaN`) are finite and non-empty, as “uniform from” presupposes, and:
--
--   1. for $(x, (\boldsymbol\epsilon, \boldsymbol\gamma))$ uniform on $B_j \times \Lambda_n$ and every word $w$ of length $n$, the probability that the first $n$ digits (`rayPrefix`) of $x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \cdots \gamma_n^{-\epsilon_n}$ are $w$ is $2/2^n$ if $j + 1 + \sum_{i=1}^{j+1} w_i$ is odd, and $0$ otherwise;
--   2. for $(x, (\boldsymbol\epsilon, \boldsymbol\gamma))$ uniform on $B'_j \times \Lambda_n$ and every word $w$ of length $j - 1$, the probability that the first $j - 1$ digits of $x \cdot \gamma_1^{\epsilon_1} \cdots \gamma_{j-1}^{\epsilon_{j-1}}$ are $w$ is $1/2^{j-1}$;
--   3. the same holds for $x \cdot \gamma_{j-1}^{\epsilon_{j-1}} \cdots \gamma_1^{\epsilon_1}$, the product in the opposite order.
--
--   Each probability is written as a number of elements divided by the size of $B_j \times \Lambda_n$ (or $B'_j \times \Lambda_n$).
--
--   Erschler and Zheng, p. 55: “Note that if we choose $\mathbf x$ uniform from $B_j$ and $(\boldsymbol\gamma, \boldsymbol\epsilon)$ uniform from $\Lambda_n$, then in $\mathbf x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \ldots \gamma_n^{-\epsilon_n}$ the distribution of the first $n$ digits is uniform on $\{0, 1\}^n$.” and p. 56: “The calculation for $\check\upsilon_n$ is similar. For $1 \leqslant j \leqslant n - k_n$, use the fact that the first $(j-1)$-digits of $x \cdot \gamma_1^{\epsilon_1} \ldots \gamma_{j-1}^{\epsilon_{j-1}}$ is uniform, we have”
--
--   *Correction.* Clause 1 as printed, uniform on all of $\{0, 1\}^n$, is false ([`ErschlerZheng.not_forall_card_rayPrefix_smul_div_card_eq_one_div_two_pow`](https://prove2.me/theorems/5368b5bb-37e4-413a-9215-2950c047f768)). Clause 1 above is the corrected form: only the words whose first $j + 1$ digits have the parity of $B_j$ occur, each with probability $2/2^n$. In the proof that follows (p. 55), the expectation in the bound $\leqslant 2^j\,\mathbb E_{\mathbf u_{\mathsf L_n}}(f(d(1^n, \mathbf z)))$ is then over that half instead of all of $\{0, 1\}^n$; [`ErschlerZheng.tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le`](https://prove2.me/theorems/c7b3368a-5992-496d-b4b7-6aae38847d40) states the resulting bound up to its constant $C$.
--
--   The set in clauses 2 and 3 is the one the υ̌ calculation uses, $\{x : (\gamma_j^{-1}, x) \notin \mathcal H\}$ with $\gamma_j = g_j$ (pp. 53 and 56). Clause 2 follows the order of the quoted sentence, $\gamma_1^{\epsilon_1} \cdots \gamma_{j-1}^{\epsilon_{j-1}}$; the displayed sums that the sentence serves, on p. 53 (“$f(d(o, x \cdot \gamma_{j-1}^{\epsilon_{j-1}} \ldots \gamma_1^{\epsilon_1}))$”) and on p. 56, write $\gamma_{j-1}^{\epsilon_{j-1}} \cdots \gamma_1^{\epsilon_1}$, and clause 3 states that order. The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), pp. 55–56, the digits are uniform, corrected

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem card_rayPrefix_smul_div_card_eq (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hjn : j + k n ≤ n) (hj : ω (j - 1) = 2) :
    (({x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} : Set Ray).Finite ∧
      ({x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} : Set Ray).Nonempty ∧
      ({x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} : Set Ray).Finite ∧
      ({x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} : Set Ray).Nonempty ∧
      Finite (LambdaN D ω k n) ∧ Nonempty (LambdaN D ω k n)) ∧
    (∀ w : List Bool, w.length = n →
      (Nat.card {q : ↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
          rayPrefix ((q.1 : Ray) <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
            fun i => ((q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat)⁻¹).prod) n = w} : ℝ) /
          Nat.card (↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
        if Odd (j + 1 + (w.take (j + 1)).count true) then 2 / 2 ^ n else 0) ∧
    (∀ w : List Bool, w.length = j - 1 →
      (Nat.card
          {q : ↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
            rayPrefix ((q.1 : Ray) <• (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
              fun i => (q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat).prod) (j - 1) = w} :
          ℝ) /
          Nat.card
            (↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
        1 / 2 ^ (j - 1)) ∧
    ∀ w : List Bool, w.length = j - 1 →
      (Nat.card
          {q : ↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
            rayPrefix ((q.1 : Ray) <• ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
              fun i => (q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat).reverse).prod) (j - 1) = w} :
          ℝ) /
          Nat.card
            (↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
        1 / 2 ^ (j - 1) := by
  sorry

end ErschlerZheng
