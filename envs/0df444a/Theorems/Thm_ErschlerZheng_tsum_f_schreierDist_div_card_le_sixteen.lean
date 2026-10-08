-- Prove2me | Theorems.Thm_ErschlerZheng_tsum_f_schreierDist_div_card_le_sixteen
-- name    : ErschlerZheng.tsum_f_schreierDist_div_card_le_sixteen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T15:27:06.546352+00:00
-- url     : https://prove2.me/theorems/51fab2c6-4b29-4e05-9bdb-ff2133de469c
-- title:
--   Lemma 7.21 with the constant 16, not in the paper — the two bounds of Lemma 7.21 hold with the factor 16 on their second terms
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), let $D$ divide $n$, let $1 \le j \le n$ with $\omega_{j-1} = \mathbf 2$ and $n < j + k_n$, and let $v \in \mathsf V^j_{2k_n}$ (`vSet`) with $|1^\infty \wedge v| \ge n - j + D$. Let $f : \mathbb R \to \mathbb R$ be non-increasing and non-negative, and let $(\boldsymbol\gamma, \boldsymbol\epsilon)$ be uniform on $\Lambda_n$ (`LambdaN`). Then for every $x$ in the orbit of $o = 1^\infty$:
--
--   1. if the germ of $\tilde g^v_j$ (`gTilde`) at $x$ is not in $\mathcal H^b$ (`letterGerms ω .b`), then $\mathbb E\, f(d(o, x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \cdots \gamma_n^{-\epsilon_n})) \le f(2^{j+2k_n}) + 16\, f(2^{n+D})\, k_n^{1+\frac2D}\, 2^{-\frac1D(j+2k_n-n)}$;
--   2. if the germ of $(\tilde g^v_j)^{-1}$ at $x$ is not in $\mathcal H^b$, then $\mathbb E\, f(d(o, x \cdot \gamma_{j-1}^{\epsilon_{j-1}} \cdots \gamma_1^{\epsilon_1})) \le f(2^{j+2k_n}) + 16\, f(2^n)\, k_n^{1+\frac2D}\, 2^{-\frac1D(j+2k_n-n)}$.
--
--   This is Lemma 7.21 of Erschler and Zheng (p. 54; the milestone [`ErschlerZheng.tsum_f_schreierDist_div_card_le`](https://prove2.me/theorems/f5846be9-5ba1-49c3-8c39-a6751914ee27)) with the factor 16 on the second term of each bound. Proposition 7.12 has a constant of its own, so this form is enough for it, and the mission's proof of Proposition 7.12 rests on it.
--
--   The paper's proof of Lemma 7.21 ends on p. 55 with "$\mathbb P(A_j(x)) \leqslant \cdots \leqslant (n-j)2^{-\frac1D(j+2k_n-n-\log_2(n-j)-\log_2 k_n)}$. In the last step we applied Lemma 7.17." Lemma 7.17 (p. 45) reads "(i): … $\leqslant 2^{-\frac1D(\ell-n)+2}$" and "(ii): … $\leqslant 8k_n2^{-\frac1D(\ell-n)}$"; the bound on p. 55 carries neither factor. Keeping them, together with a factor 2 from rounding the level down to an integer, gives the constant 16 of this statement. Whether Lemma 7.21 holds as printed, with the constant 1, is open.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 54, Lemma 7.21 with the constant 16 on the second term of each bound (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

open scoped RightActions

namespace ErschlerZheng

theorem tsum_f_schreierDist_div_card_le_sixteen (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (v : List Bool)
    (hv : v ∈ vSet D ω j (2 * k n)) (hv' : n - j + D ≤ commonPrefixLength v oneRay)
    (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ s, 0 ≤ f s) :
    (∀ x ∈ orbitOne ω, (gTilde ω j v, x) ∉ letterGerms ω .b →
      (∑' p : LambdaN D ω k n, f (schreierDist ω oneRay
          (x <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map fun i =>
            ((p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod))) /
          Nat.card (LambdaN D ω k n) ≤
        f (2 ^ (j + 2 * k n)) +
          16 * (f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)))) ∧
    ∀ x ∈ orbitOne ω, ((gTilde ω j v)⁻¹, x) ∉ letterGerms ω .b →
      (∑' p : LambdaN D ω k n, f (schreierDist ω oneRay
          (x <• (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).reverse.map fun i =>
            (p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat).prod))) /
          Nat.card (LambdaN D ω k n) ≤
        f (2 ^ (j + 2 * k n)) +
          16 * (f (2 ^ n) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n))) := by
  sorry

end ErschlerZheng
