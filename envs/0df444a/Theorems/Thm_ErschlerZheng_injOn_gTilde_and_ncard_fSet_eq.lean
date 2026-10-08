-- Prove2me | Theorems.Thm_ErschlerZheng_injOn_gTilde_and_ncard_fSet_eq
-- name    : ErschlerZheng.injOn_gTilde_and_ncard_fSet_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T05:11:44.219401+00:00
-- url     : https://prove2.me/theorems/0c7a2721-11c0-49ac-987c-082656e7fb60
-- title:
--   p. 40 — 𝔉_{j,n} is indexed by the v ∈ V^j_{2k_n} with prefix 1^{n−j+D}, distinct indices give distinct g̃^v_j, and |𝔉_{j,n}| = 2^{(2k_n − (n−j+j̄))/D}
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), let $D$ divide $n$, and let $1 \le j \le n$ with $\omega_{j-1} = \mathbf 2$ and $n - k_n < j$ (written $n < j + k_n$). Write $P$ for the set of $v \in \mathsf V^j_{2k_n}$ (`vSet`) with $|1^\infty \wedge v| \ge n - j + D$ (`commonPrefixLength`). Then:
--
--   1. $P$ is the set of $v \in \mathsf V^j_{2k_n}$ having $1^{n-j+D}$ as a prefix;
--   2. $v \mapsto \tilde g^v_j$ (`gTilde`) is injective on $P$;
--   3. $\mathfrak F_{j,n}$ (`fSet`) has $2^{(2k_n - (n-j+\bar j))/D}$ elements, where $\bar j$ is the residue of $j$ mod $D$.
--
--   Erschler and Zheng, p. 40, after (7.7): “The set $\mathfrak F_{j,n}$ is indexed by the subset of $\mathsf V^j_{2k_n}$ which consists of vertices with prefix $1^{n-j+D}$. The cardinality of $\mathfrak F_{j,n}$ is $2^{\frac{2k_n - (n-j+\bar j)}{D}}$ in this case.”
--
--   “Indexed by” is read as clauses 1 and 2: the index set of (7.7), defined by $|1^\infty \wedge v| \ge n - j + D$, is the set of vertices with prefix $1^{n-j+D}$, and different indices give different elements. The exponent is computed in $\mathbb N$, where its subtractions are exact ([`ErschlerZheng.dvd_sub_add_mod_and_sub_add_mod_lt_two_mul_and_dvd_two_mul_sub_of_isAdmissibleSeq`](https://prove2.me/theorems/53ba880d-78e2-4382-a2b6-17c770721bb6)). The hypotheses on $j$ are those of the first case of (7.7), the case the sentence refers to. The assumption $(\mathrm{Fr}(D))$ is the standing assumption of §7.2 (p. 35).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 40, the sets (7.7)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem injOn_gTilde_and_ncard_fSet_eq (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) :
    {v ∈ vSet D ω j (2 * k n) | n - j + D ≤ commonPrefixLength v oneRay} =
      {v ∈ vSet D ω j (2 * k n) | List.replicate (n - j + D) true <+: v} ∧
    Set.InjOn (gTilde ω j) {v ∈ vSet D ω j (2 * k n) | n - j + D ≤ commonPrefixLength v oneRay} ∧
    (fSet D ω k j n).ncard = 2 ^ ((2 * k n - (n - j + j % D)) / D) := by
  sorry

end ErschlerZheng
