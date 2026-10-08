-- Prove2me | Theorems.Thm_ErschlerZheng_tsum_f_schreierDist_div_card_le
-- name    : ErschlerZheng.tsum_f_schreierDist_div_card_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-06T08:31:02.328111+00:00
-- url     : https://prove2.me/theorems/f5846be9-5ba1-49c3-8c39-a6751914ee27
-- title:
--   Lemma 7.21, for f ⩾ 0 — at a bad point x of g̃^v_j, E f(d(o, x·γ_{j+1}^{−ε_{j+1}}⋯γ_n^{−ε_n})) ⩽ f(2^{j+2k_n}) + f(2^{n+D}) k_n^{1+2/D} 2^{−(j+2k_n−n)/D}; likewise for its inverse
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), let $D$ divide $n$, let $1 \le j \le n$ with $\omega_{j-1} = \mathbf 2$ and $n - k_n < j$ (written $n < j + k_n$), and let $v \in \mathsf V^j_{2k_n}$ (`vSet`) with $|1^\infty \wedge v| \ge n - j + D$, so that $\tilde g^v_j$ (`gTilde`) is an element of $\mathfrak F_{j,n}$. Let $f : \mathbb R \to \mathbb R$ be non-increasing (`Antitone`) and non-negative. Write $d$ for the Schreier distance (`schreierDist`), $o = 1^\infty$, and $\mathbb E$ for the average over $(\boldsymbol\epsilon, \boldsymbol\gamma) \in \Lambda_n$ (`LambdaN`), written as a sum divided by $|\Lambda_n|$. Then for every $x$ in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`):
--
--   1. if the germ of $\tilde g^v_j$ at $x$ is not in $\mathcal H^b$ (`letterGerms ω .b`), then $\mathbb E\, f(d(o, x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \cdots \gamma_n^{-\epsilon_n})) \le f(2^{j+2k_n}) + f(2^{n+D})\, k_n^{1+\frac2D}\, 2^{-\frac1D(j+2k_n-n)}$;
--   2. if the germ of $(\tilde g^v_j)^{-1}$ at $x$ is not in $\mathcal H^b$, then $\mathbb E\, f(d(o, x \cdot \gamma_{j-1}^{\epsilon_{j-1}} \cdots \gamma_1^{\epsilon_1})) \le f(2^{j+2k_n}) + f(2^n)\, k_n^{1+\frac2D}\, 2^{-\frac1D(j+2k_n-n)}$.
--
--   Erschler and Zheng, p. 54, Lemma 7.21: “Let $n - k_n < j \leqslant n$ be a level such that $\omega_{j-1} = \mathbf 2$ and $\tilde g^v_j \in \mathfrak F_{j,n}$. Suppose $f : \mathbb R \to \mathbb R$ is a non-increasing function. Let $(\boldsymbol\gamma, \boldsymbol\epsilon)$ be a random variable with uniform distribution on the set $\Lambda_n$ defined in (7.9). (i): Let $x$ be a point such that $(\tilde g^v_j, x) \notin \mathcal H$, then $\mathbb E(f(d(o, x \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \ldots \gamma_n^{-\epsilon_n}))) \leqslant f(2^{j+2k_n}) + f(2^{n+D})k_n^{1+\frac2D}2^{-\frac1D(j+2k_n-n)}$. (ii): Let $x$ be a point such that $((\tilde g^v_j)^{-1}, x) \notin \mathcal H$, then $\mathbb E(f(d(o, x \cdot \gamma_{j-1}^{\epsilon_{j-1}} \ldots \gamma_1^{\epsilon_1}))) \leqslant f(2^{j+2k_n}) + f(2^n)k_n^{1+\frac2D}2^{-\frac1D(j+2k_n-n)}$.”
--
--   *Correction.* As printed, for every non-increasing $f : \mathbb R \to \mathbb R$, the lemma fails ([`ErschlerZheng.not_forall_tsum_f_schreierDist_div_card_le_of_antitone`](https://prove2.me/theorems/51ae8884-4cfa-4a15-82e7-e84d7558aee6)). The statement adds $f \ge 0$; every use has $f \ge 0$ (Proposition 7.12 takes $f : \mathbb R_+ \to \mathbb R_+$, p. 43).
--
--   The index $v$ is a hypothesis because $\tilde g^v_j \in \mathfrak F_{j,n}$ names it: $v \in \mathsf V^j_{2k_n}$ with $|1^\infty \wedge v| \ge n - j + D$, the index set of (7.7). $\mathcal H$ is $\mathcal H^b$ (p. 42). The standing assumptions are those of §7.2 (pp. 35 and 40).
--
--   *Gap.* The proof ends on p. 55 with “$\mathbb P(A_j(x)) \leqslant \cdots \leqslant (n-j)2^{-\frac1D(j+2k_n-n-\log_2(n-j)-\log_2 k_n)}$. In the last step we applied Lemma 7.17.” Lemma 7.17 (p. 45) bounds by “$2^{-\frac1D(\ell-n)+2}$” in (i) and by “$8k_n2^{-\frac1D(\ell-n)}$” in (ii), and the bound on p. 55 carries neither factor. Keeping them, together with a factor 2 from rounding the level down to an integer, the lemma holds with the factor 16 on the second term of each bound ([`ErschlerZheng.tsum_f_schreierDist_div_card_le_sixteen`](https://prove2.me/theorems/51fab2c6-4b29-4e05-9bdb-ff2133de469c)). That is enough for Proposition 7.12, whose constant absorbs the 16, and the mission's proof of Proposition 7.12 uses it. Whether the lemma holds as printed, with the constant 1, is open.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 54, Lemma 7.21, for f ⩾ 0

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem tsum_f_schreierDist_div_card_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
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
          f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n))) ∧
    ∀ x ∈ orbitOne ω, ((gTilde ω j v)⁻¹, x) ∉ letterGerms ω .b →
      (∑' p : LambdaN D ω k n, f (schreierDist ω oneRay
          (x <• (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).reverse.map fun i =>
            (p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat).prod))) /
          Nat.card (LambdaN D ω k n) ≤
        f (2 ^ (j + 2 * k n)) +
          f (2 ^ n) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)) := by
  sorry

end ErschlerZheng
