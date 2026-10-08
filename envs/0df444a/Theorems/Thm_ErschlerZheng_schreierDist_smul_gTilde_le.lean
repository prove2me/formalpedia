-- Prove2me | Theorems.Thm_ErschlerZheng_schreierDist_smul_gTilde_le
-- name    : ErschlerZheng.schreierDist_smul_gTilde_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T05:55:43.265254+00:00
-- url     : https://prove2.me/theorems/2db189f0-85aa-487a-847e-1750800a64bf
-- title:
--   Lemma 7.16 — for g̃^v_j ∈ 𝔉_{j,n} and x ∈ 1^∞·G, d_𝒮(x, x·g̃^v_j) ⩽ 2^{j+|𝔰^{j+1}x ∧ 𝔰v|+4} or 2^{j+2}, according as |𝔰^{j+1}x ∧ 𝔰v| ⩾ n − j + D or not
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), let $D$ divide $n$, and let $1 \le j \le n$ with $\omega_{j-1} = \mathbf 2$ and $n - k_n < j$ (written $n < j + k_n$). Let $v \in \mathsf V^j_{2k_n}$ (`vSet`) with $|1^\infty \wedge v| \ge n - j + D$, so that $\tilde g^v_j$ (`gTilde`) is an element of $\mathfrak F_{j,n}$, and let $x$ be a ray in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`). Write $L = |\mathfrak s^{j+1}x \wedge \mathfrak sv|$ for the length of the common prefix of $x_{j+2}x_{j+3}\ldots$ (`shiftRay x (j + 1)`) and $v_2 v_3 \ldots$ (`List.drop 1 v`). Then the Schreier distance (`schreierDist`) satisfies
--   $$d_{\mathcal S}(x, x \cdot \tilde g^v_j) \le 2^{j+L+4} \ \text{ if } L \ge n - j + D, \qquad d_{\mathcal S}(x, x \cdot \tilde g^v_j) \le 2^{j+2} \ \text{ if } L < n - j + D.$$
--
--   Erschler and Zheng, p. 44, Lemma 7.16: “Let $j$ be an index such that $\omega_{j-1} = \mathbf 2$ and $n - k_n < j \leqslant n$. Let $\tilde g^v_j \in \mathfrak F_{j,n}$, then for any $x \in 1^\infty \cdot G$, $d_{\mathcal S}(x, x \cdot \tilde g^v_j) \leqslant 2^{j+|\mathfrak s^{j+1}x \wedge \mathfrak sv|+4}$ if $|\mathfrak s^{j+1}x \wedge \mathfrak sv| \geqslant n - j + D$, $2^{j+2}$ if $|\mathfrak s^{j+1}x \wedge \mathfrak sv| < n - j + D$.”
--
--   The bound depends on the index $v$, so the statement takes $v$ rather than the element: $\tilde g^v_j \in \mathfrak F_{j,n}$ is written as $v \in \mathsf V^j_{2k_n}$ with $|1^\infty \wedge v| \ge n - j + D$, the index set of (7.7). $\mathfrak s$ is the shift on strings (Fact 7.4, p. 35), applied to the vertex $v$ as dropping its first digit. The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 44, Lemma 7.16

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem schreierDist_smul_gTilde_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (v : List Bool)
    (hv : v ∈ vSet D ω j (2 * k n)) (hv' : n - j + D ≤ commonPrefixLength v oneRay) (x : Ray)
    (hx : x ∈ orbitOne ω) :
    (n - j + D ≤ commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) →
      schreierDist ω x (x <• gTilde ω j v) ≤
        2 ^ (j + commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 4)) ∧
    (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) < n - j + D →
      schreierDist ω x (x <• gTilde ω j v) ≤ 2 ^ (j + 2)) := by
  sorry

end ErschlerZheng
