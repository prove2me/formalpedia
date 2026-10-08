-- Prove2me | Theorems.Thm_ErschlerZheng_mass_uniformMeasure_fSet_le_and_card_fProd_le
-- name    : ErschlerZheng.mass_uniformMeasure_fSet_le_and_card_fProd_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T06:26:39.802786+00:00
-- url     : https://prove2.me/theorems/2698c9e3-f6ce-4425-8b6f-42339d91dd78
-- title:
--   Lemma 7.17 — tail bounds: u_{𝔉_{j,n}}(d_𝒮(x, x·γ) ⩾ 2^ℓ) ⩽ 2^{−(ℓ−n)/D+2} and u_{𝔉_n}(d_𝒮(x, x·γ_n^{ε_n}⋯γ_1^{ε_1}) ⩾ k_n 2^ℓ) ⩽ 8k_n 2^{−(ℓ−n)/D}
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), and let $n \ge 1$ be divisible by $D$. For rays $x$ in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) and the Schreier distance $d_{\mathcal S}$ (`schreierDist`):
--
--   1. for every $1 \le j \le n$ with $n - k_n \le j$ (written $n \le j + k_n$) and $\omega_{j-1} = \mathbf 2$, every $\ell$ with $n \le \ell \le j + 2k_n + 2D + 4$ and every such $x$, the uniform measure on $\mathfrak F_{j,n}$ (`uniformMeasure (fSet …)`) gives the set $\{\gamma : d_{\mathcal S}(x, x \cdot \gamma) \ge 2^\ell\}$ mass at most $2^{-(\ell - n)/D + 2}$;
--   2. for every $\boldsymbol\epsilon \in \{0, 1\}^n$, every $\ell$ with $n \le \ell \le n + 2k_n + 2D + 5$ and every such $x$, the proportion of $\boldsymbol\gamma \in \mathfrak F_n$ (`fProd`) with $d_{\mathcal S}(x, x \cdot \gamma_n^{\epsilon_n} \cdots \gamma_1^{\epsilon_1}) \ge k_n 2^\ell$ (`theta`) is at most $8k_n 2^{-(\ell - n)/D}$.
--
--   Erschler and Zheng, p. 45, Lemma 7.17: “We have the following upper bounds: (i): Let $j$ be a level such that $n - k_n \leqslant j \leqslant n$ and $\omega_{j-1} = \mathbf 2$. For any $\ell$ such that $n \leqslant \ell \leqslant j + 2k_n + 2D + 4$ and $x \in 1^\infty \cdot G$, $\mathbf u_{\mathfrak F_{j,n}}(\{\gamma : d_{\mathcal S}(x, x \cdot \gamma) \geqslant 2^\ell\}) \leqslant 2^{-\frac1D(\ell-n)+2}$. (ii): For any $(\epsilon_1, \ldots, \epsilon_n) \in \{0, 1\}^n$, $n \leqslant \ell \leqslant n + 2k_n + 2D + 5$ and $x \in 1^\infty \cdot G$, $\mathbf u_{\mathfrak F_n}(\{\boldsymbol\gamma : d_{\mathcal S}(x, x \cdot \gamma_n^{\epsilon_n} \ldots \gamma_1^{\epsilon_1}) \geqslant k_n2^\ell\}) \leqslant 8k_n2^{-\frac1D(\ell-n)}$.”
--
--   The range of $j$ in (i) is the printed one, $n - k_n \leqslant j$. At $j = n - k_n$ the first case of (7.7) does not apply, so $\mathfrak F_{j,n} = \{g_j\}$; the statement includes that index, as printed. The uniform measure on $\mathfrak F_n = \prod_i \mathfrak F_{i,n}$ is written as a proportion of its elements. The statement assumes $n \ge 1$, which part (ii) cannot drop ([`ErschlerZheng.not_forall_card_fProd_le`](https://prove2.me/theorems/f065b48f-f15d-4acc-b21b-b10cf28ae48b)). Every $n$ the paper uses is positive. The other standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 45, Lemma 7.17

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem mass_uniformMeasure_fSet_le_and_card_fProd_le (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n)
    (hn1 : 1 ≤ n) :
    (∀ j, 1 ≤ j → n ≤ j + k n → j ≤ n → ω (j - 1) = 2 →
      ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ j + 2 * k n + 2 * D + 4 → ∀ x ∈ orbitOne ω,
        mass (uniformMeasure (fSet D ω k j n)) {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} ≤
          (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 2)) ∧
    ∀ ε : Fin n → Bool, ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ n + 2 * k n + 2 * D + 5 → ∀ x ∈ orbitOne ω,
      (Nat.card {γ : fProd D ω k n // k n * 2 ^ ℓ ≤ schreierDist ω x (x <• theta D ω k n (ε, γ))} :
          ℝ) / Nat.card (fProd D ω k n) ≤
        8 * k n * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by
  sorry

end ErschlerZheng
