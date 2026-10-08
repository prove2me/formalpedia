-- Prove2me | Theorems.Thm_ErschlerZheng_schreierDist_smul_le_of_mem_fSet_and_smul_theta_le
-- name    : ErschlerZheng.schreierDist_smul_le_of_mem_fSet_and_smul_theta_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T06:09:34.412576+00:00
-- url     : https://prove2.me/theorems/7c29fd7f-3b80-4f66-b3ff-85bcea43e215
-- title:
--   p. 45 — the maximal displacements: d_𝒮(x, x·γ) ⩽ 2^{j+2k_n+2D+4} for γ ∈ 𝔉_{j,n}, and d_𝒮(x, x·θ_n(ε, γ)) ⩽ 2^{n+2k_n+2D+5}
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), and let $D$ divide $n$. Then, for the Schreier distance $d_{\mathcal S}$ (`schreierDist`) and rays $x$ in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`):
--
--   1. for every $1 \le j \le n$, every $\gamma \in \mathfrak F_{j,n}$ (`fSet`) and every such $x$: $d_{\mathcal S}(x, x \cdot \gamma) \le 2^{j+2k_n+2D+4}$;
--   2. for every such $x$ and every $(\boldsymbol\epsilon, \boldsymbol\gamma) \in \Lambda_n$ (`LambdaN`): $d_{\mathcal S}(x, x \cdot \gamma_n^{\epsilon_n} \cdots \gamma_1^{\epsilon_1}) \le 2^{n+2k_n+2D+5}$ (`theta`).
--
--   Erschler and Zheng, p. 45: “Lemma 7.16 implies that $\max_{\gamma \in \mathfrak F_{j,n}} d_{\mathcal S}(x, x \cdot \gamma) \leqslant 2^{j+2k_n+2D+4}$. By the triangle inequality, for any $x$ and $\boldsymbol\epsilon \in \{0, 1\}^n$, $\max_{\boldsymbol\gamma \in \mathfrak F_n} d_{\mathcal S}(x, x \cdot \gamma_n^{\epsilon_n} \ldots \gamma_1^{\epsilon_1}) \leqslant 2^{n+2k_n+2D+5}$.”
--
--   The first bound is stated for every level $1 \le j \le n$, as the triangle-inequality step uses it. On the levels of Lemma 7.16 ($\omega_{j-1} = \mathbf 2$ and $n - k_n < j$, the first case of (7.7)) it is that lemma's bound. On every other level $\mathfrak F_{j,n} = \{g_j\}$, and the proof of Lemma 7.16 on the same page gives $d_{\mathcal S}(x, x \cdot g_j) \leqslant 2^{j+2}$, which the proof of Lemma 7.17(ii) also uses for these levels. The points $x$ are those of $1^\infty \cdot G$, as in Lemma 7.16. A maximum bounded by a constant is written as the bound for every element. The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 45, the maximal displacements

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem schreierDist_smul_le_of_mem_fSet_and_smul_theta_le (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) :
    (∀ j, 1 ≤ j → j ≤ n → ∀ γ ∈ fSet D ω k j n, ∀ x ∈ orbitOne ω,
        schreierDist ω x (x <• γ) ≤ 2 ^ (j + 2 * k n + 2 * D + 4)) ∧
    ∀ x ∈ orbitOne ω, ∀ p : LambdaN D ω k n,
      schreierDist ω x (x <• theta D ω k n p) ≤ 2 ^ (n + 2 * k n + 2 * D + 5) := by
  sorry

end ErschlerZheng
