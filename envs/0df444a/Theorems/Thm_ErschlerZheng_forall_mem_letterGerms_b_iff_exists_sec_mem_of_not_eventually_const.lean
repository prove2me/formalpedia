-- Prove2me | Theorems.Thm_ErschlerZheng_forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const
-- name    : ErschlerZheng.forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T03:10:34.438107+00:00
-- url     : https://prove2.me/theorems/343f858e-11fc-4b3b-8737-c37be4fd3bb3
-- title:
--   p. 42 — for ω not eventually constant, g ∈ G_ω has only ⟨b⟩-germs iff at some level n all its sections lie in {id, a, b_{𝔰^nω}}
-- statement:
--   Let $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$ be a string that is not eventually constant and let $g \in G_\omega$. Then $(g, x)$ belongs to the groupoid $\mathcal H^b$ of $\langle b \rangle$-germs (`letterGerms ω .b`) for every $x$ in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) if and only if there is a level $n$ such that for every vertex $v$ of level $n$ the section $g_v$ (`sec`) is $id$, $a$ or $b_{\mathfrak s^n\omega}$.
--
--   Erschler and Zheng, p. 42: “Recall that as explained in Example 3.2, the isotropy group of the groupoid of germs of $G_\omega \curvearrowright \partial \mathsf T$ at $1^\infty$ is isomorphic to $\mathbb Z/2\mathbb Z \times \mathbb Z/2\mathbb Z = \langle b \rangle \times \langle c \rangle$. An element $g \in G_\omega$ has only $\langle b \rangle$-germs if and only if there is a level $n$ such that all sections $g_v$ are in $\{id, a, b_{\mathfrak s^n\omega}\}$, $v \in \mathsf L_n$.”
--
--   The phrase “has only $\langle b \rangle$-germs” is read as $(g, x) \in \mathcal H^b$ at every point $x$ of the orbit of $1^\infty$, the groupoid $\mathcal H^b = \mathcal H(\langle b \rangle)$ of Example 3.2 with the finitary automorphisms as auxiliary group. The hypothesis that $\omega$ is not eventually constant is the case of Example 3.2 in which $\langle b \rangle$ is a proper subgroup of $\hat{\mathcal G}_o$; it holds under Assumption $(\mathrm{Fr}(D))$, the standing assumption of §7 ([`ErschlerZheng.exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr`](https://prove2.me/theorems/10b40a56-7193-4cf0-8ff5-5ebe2179a42c)). For the first Grigorchuk group the same criterion is Fact 4.1 (p. 21); for general $\omega$ the paper states it without proof.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 42, germs read from sections

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const (ω : ℕ → Fin 3)
    (hω : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i) (g : Garrido.BinaryTreeAut)
    (hg : g ∈ grigorchuk ω) :
    (∀ x ∈ orbitOne ω, (g, x) ∈ letterGerms ω .b) ↔
      ∃ n, ∀ v : List Bool, v.length = n →
        sec g v ∈ ({1, Garrido.grigA, gen (shiftSeq ω n) .b} : Set Garrido.BinaryTreeAut) := by
  sorry

end ErschlerZheng
