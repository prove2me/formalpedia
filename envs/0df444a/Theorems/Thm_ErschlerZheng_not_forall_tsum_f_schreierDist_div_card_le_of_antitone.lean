-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_tsum_f_schreierDist_div_card_le_of_antitone
-- name    : ErschlerZheng.not_forall_tsum_f_schreierDist_div_card_le_of_antitone
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:18.073502+00:00
-- url     : https://prove2.me/theorems/51ae8884-4cfa-4a15-82e7-e84d7558aee6
-- title:
--   Lemma 7.21, as printed, fails — for non-increasing f : ℝ → ℝ taking negative values the bound (i) can fail
-- statement:
--   It is not true that for every $D$, every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), every sequence $(k_n)$ satisfying the standing assumption of p. 40 (`IsAdmissibleSeq`), every $n$ divisible by $D$, every $1 \le j \le n$ with $\omega_{j-1} = \mathbf 2$ and $n - k_n < j$, every $v \in \mathsf V^j_{2k_n}$ (`vSet`) with $|1^\infty \wedge v| \ge n - j + D$, every non-increasing $f : \mathbb R \to \mathbb R$ (`Antitone`) and every point $x$ of the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) at which the germ of $\tilde g^v_j$ (`gTilde`) is not in $\mathcal H^b$ (`letterGerms ω .b`), the average over $(\boldsymbol\epsilon, \boldsymbol\gamma) \in \Lambda_n$ (`LambdaN`) of $f(d(o, x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \cdots \gamma_n^{-\epsilon_n}))$ is at most $f(2^{j+2k_n}) + f(2^{n+D})\, k_n^{1+\frac2D}\, 2^{-\frac1D(j+2k_n-n)}$. Here $d$ is the Schreier distance (`schreierDist`) and $o = 1^\infty$.
--
--   Erschler and Zheng, p. 54, Lemma 7.21: “Let $n - k_n < j \leqslant n$ be a level such that $\omega_{j-1} = \mathbf 2$ and $\tilde g^v_j \in \mathfrak F_{j,n}$. Suppose $f : \mathbb R \to \mathbb R$ is a non-increasing function. Let $(\boldsymbol\gamma, \boldsymbol\epsilon)$ be a random variable with uniform distribution on the set $\Lambda_n$ defined in (7.9). (i): Let $x$ be a point such that $(\tilde g^v_j, x) \notin \mathcal H$, then $\mathbb E(f(d(o, x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \ldots \gamma_n^{-\epsilon_n}))) \leqslant f(2^{j+2k_n}) + f(2^{n+D})k_n^{1+\frac2D}2^{-\frac1D(j+2k_n-n)}$.”
--
--   The statement is the negation of part (i) as printed, for every non-increasing real function. The corrected lemma, for non-negative $f$, is the milestone `ErschlerZheng.tsum_f_schreierDist_div_card_le`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 54, Lemma 7.21 (i) as printed (fails for negative f)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

open scoped RightActions

namespace ErschlerZheng

theorem not_forall_tsum_f_schreierDist_div_card_le_of_antitone :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      ∀ n, D ∣ n → ∀ j, 1 ≤ j → ω (j - 1) = 2 → n < j + k n → j ≤ n →
      ∀ v ∈ vSet D ω j (2 * k n), n - j + D ≤ commonPrefixLength v oneRay →
      ∀ f : ℝ → ℝ, Antitone f → ∀ x ∈ orbitOne ω, (gTilde ω j v, x) ∉ letterGerms ω .b →
        (∑' p : LambdaN D ω k n, f (schreierDist ω oneRay
            (x <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map fun i =>
              ((p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod))) /
            Nat.card (LambdaN D ω k n) ≤
          f (2 ^ (j + 2 * k n)) +
            f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
              (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)) := by
  sorry

end ErschlerZheng
