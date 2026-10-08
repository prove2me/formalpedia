-- Prove2me | Theorems.Thm_ErschlerZheng_vertex_smul_eq_smul_seqG_of_mem_fSet
-- name    : ErschlerZheng.vertex_smul_eq_smul_seqG_of_mem_fSet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T05:26:45.472447+00:00
-- url     : https://prove2.me/theorems/5ff437e9-3c4d-4a9f-8577-fe31be283399
-- title:
--   Fact 7.14 — on level n + D + 1, every element of 𝔉_{j,n} acts as g_j
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), let $D$ divide $n$, and let $1 \le j \le n$ with $\omega_{j-1} = \mathbf 2$ and $n - k_n < j$ (written $n < j + k_n$). Then every $\gamma \in \mathfrak F_{j,n}$ (`fSet`) acts on the vertices of level $n + D + 1$ as $g_j$ (`seqG`) does: $u \cdot \gamma = u \cdot g_j$ for every vertex $u$ of length $n + D + 1$.
--
--   Erschler and Zheng, p. 44, Fact 7.14: “Let $j$ be an index such that $\omega_{j-1} = \mathbf 2$ and $n - k_n < j \leqslant n$. Then on the finite level $n + D + 1$, the action of any element $\tilde g^v_j \in \mathfrak F_{j,n}$ is the same as the element $g_j$.”
--
--   The standing assumptions are those of §7.2: $(\mathrm{Fr}(D))$ (p. 35) and, on p. 40, “Let $(k_n)$ be a sequence of increasing positive integers divisible by $D$ to be determined later, $k_n \ll n$. In what follows $n$ is always an integer divisible by $D$.” The index $j$ lies in $\{1, \ldots, n\}$, the range of (7.7).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 44, Fact 7.14

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem vertex_smul_eq_smul_seqG_of_mem_fSet (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (γ : Garrido.BinaryTreeAut)
    (hγ : γ ∈ fSet D ω k j n) (u : List Bool) (hu : u.length = n + D + 1) :
    u <• γ = u <• seqG ω j := by
  sorry

end ErschlerZheng
