-- Prove2me | Theorems.Thm_ErschlerZheng_isCubeIndependent_of_mem_levelStab_of_rootPerm_ne
-- name    : ErschlerZheng.isCubeIndependent_of_mem_levelStab_of_rootPerm_ne
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T01:46:33.098985+00:00
-- url     : https://prove2.me/theorems/8c49f339-ea0c-4914-8b44-9ca664b072bd
-- title:
--   Lemma 5.6 — if g_n ∈ St_G(L_n) and its sections at level n have fixed-point-free root permutations, (g_n) is cube independent on 1^∞·G
-- statement:
--   Let $\mathbf d = (d_j)$ be a sequence with $d_j \ge 2$ for every $j$, let $G$ be a subgroup of $\mathrm{Aut}(\mathsf T_{\mathbf d})$ (`SphericalTreeAut d`), and let $g_1, g_2, \ldots$ be automorphisms such that, for every $n \ge 1$: $g_n \in G$; $g_n$ fixes every vertex of level $n$; and for every vertex $v$ of level $n$ the root permutation of the section $(g_n)_v$ (`rootPerm (sphericalSec (g n) v)`) has no fixed point. Then $(g_n)$ has the cube independence property on the orbit $1^\infty \cdot G$ (`IsCubeIndependent` with parameters $k_n = 1$): for every $n \ge 1$ and every $x \in 1^\infty \cdot G$, the $2^n$ rays $x \cdot g_n^{\varepsilon_n} \cdots g_1^{\varepsilon_1}$, $(\varepsilon_1, \ldots, \varepsilon_n) \in \{0, 1\}^n$, are distinct.
--
--   Erschler and Zheng, p. 27, Lemma 5.6: “Let $G < \mathrm{Aut}(\mathsf T_d)$ and suppose that $g_n \in G$ satisfies that $g_n \in \mathrm{St}_G(\mathsf L_n)$ and the root permutation of the section $(g_n)_v$ has no fixed point for all $v \in \mathsf L_n$. Then the sequence $(g_n)_{n \geqslant 0}$ has the cube independence property on $1^\infty \cdot G$.”
--
--   The sequence is indexed from $1$, as in the definition of the cube independence property (“For a sequence of elements $g_1, g_2, \ldots \in G$”, p. 26), and the hypotheses are for $n \ge 1$; the term $g_0$ plays no role. Membership in $\mathrm{St}_G(\mathsf L_n)$ is written out as $g_n \in G$ fixing every vertex of level $n$. For the binary tree the same lemma is the milestone [`ErschlerZheng.isCubeIndependent_of_mem_levelStab_of_sec_smul_ne`](https://prove2.me/theorems/ec438088-d3ae-4362-b0a2-68014baa01cd).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 27, Lemma 5.6

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
open scoped RightActions

namespace ErschlerZheng

theorem isCubeIndependent_of_mem_levelStab_of_rootPerm_ne (d : ℕ → ℕ) (hd : ∀ j, 2 ≤ d j)
    (G : Subgroup (SphericalTreeAut d)) (g : ℕ → SphericalTreeAut d)
    (hgG : ∀ n, 1 ≤ n → g n ∈ G)
    (hstab : ∀ n, 1 ≤ n → ∀ v : SphericalVertex d, v.1.length = n → v <• g n = v)
    (hroot : ∀ n, 1 ≤ n → ∀ v : SphericalVertex d, v.1.length = n →
      ∀ j, rootPerm (sphericalSec (g n) v) j ≠ j) :
    IsCubeIndependent (rightOrbit G (sphericalOneRay d hd)) (fun _ => 1) g := by
  sorry

end ErschlerZheng
