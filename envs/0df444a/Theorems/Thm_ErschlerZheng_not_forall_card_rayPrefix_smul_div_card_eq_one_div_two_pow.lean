-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_card_rayPrefix_smul_div_card_eq_one_div_two_pow
-- name    : ErschlerZheng.not_forall_card_rayPrefix_smul_div_card_eq_one_div_two_pow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:34.904205+00:00
-- url     : https://prove2.me/theorems/5368b5bb-37e4-413a-9215-2950c047f768
-- title:
--   p. 55, as printed, fails — the first n digits of x·γ_{j+1}^{−ε_{j+1}}⋯γ_n^{−ε_n}, x uniform on B_j, are not uniform on {0,1}^n
-- statement:
--   It is not true that for every $D$, every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), every sequence $(k_n)$ satisfying the standing assumption of p. 40 (`IsAdmissibleSeq`), every $n$ divisible by $D$, every $1 \le j \le n - k_n$ with $\omega_{j-1} = \mathbf 2$ for which $B_j \times \Lambda_n$ (`LambdaN`) is finite and non-empty, and every word $w$ of length $n$: for $(x, (\boldsymbol\epsilon, \boldsymbol\gamma))$ uniform on $B_j \times \Lambda_n$, the first $n$ digits (`rayPrefix`) of $x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \cdots \gamma_n^{-\epsilon_n}$ are $w$ with probability $1/2^n$. Here $B_j$ is the set of points $x$ of the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) at which the germ of $g_j$ (`seqG`) is not in $\mathcal H^b$ (`letterGerms ω .b`), and the probability is written as a number of elements divided by the size of $B_j \times \Lambda_n$.
--
--   Erschler and Zheng, p. 55: “Note that if we choose $\mathbf x$ uniform from $B_j$ and $(\boldsymbol\gamma, \boldsymbol\epsilon)$ uniform from $\Lambda_n$, then in $\mathbf x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \ldots \gamma_n^{-\epsilon_n}$ the distribution of the first $n$ digits is uniform on $\{0, 1\}^n$.”
--
--   The statement is the negation of this claim as printed, with the sentence's setting “$1 \leqslant j \leqslant n - k_n$ and $\omega_{j-1} = \mathbf 2$” (p. 55). “Uniform from $B_j$” and “uniform from $\Lambda_n$” presuppose finite non-empty sets, and the statement keeps that presupposition: the size of $B_j \times \Lambda_n$ is required to be positive, which in Lean says it is finite and non-empty, so the claim cannot fail merely because a size of $0$ appears in a quotient. The corrected claim, uniform on the half of $\{0, 1\}^n$ whose first $j + 1$ digits have the parity of $B_j$, is the milestone `ErschlerZheng.card_rayPrefix_smul_div_card_eq`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 55, the digits are uniform, as printed (fails)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

open scoped RightActions

namespace ErschlerZheng

theorem not_forall_card_rayPrefix_smul_div_card_eq_one_div_two_pow :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      ∀ n, D ∣ n → ∀ j, 1 ≤ j → j + k n ≤ n → ω (j - 1) = 2 →
      0 < Nat.card (↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n) →
      ∀ w : List Bool, w.length = n →
        (Nat.card
            {q : ↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
              rayPrefix ((q.1 : Ray) <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
                fun i => ((q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat)⁻¹).prod) n = w} :
            ℝ) /
            Nat.card (↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
          1 / 2 ^ n := by
  sorry

end ErschlerZheng
