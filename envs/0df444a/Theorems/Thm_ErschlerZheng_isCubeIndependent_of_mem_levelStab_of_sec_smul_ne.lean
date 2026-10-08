-- Prove2me | Theorems.Thm_ErschlerZheng_isCubeIndependent_of_mem_levelStab_of_sec_smul_ne
-- name    : ErschlerZheng.isCubeIndependent_of_mem_levelStab_of_sec_smul_ne
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T01:58:51.364141+00:00
-- url     : https://prove2.me/theorems/ec438088-d3ae-4362-b0a2-68014baa01cd
-- title:
--   Lemma 5.6, for the binary tree — if g_n ∈ St_G(L_n) and its sections at level n swap the two subtrees, (g_n) is cube independent on 1^∞·G
-- statement:
--   Let $G$ be a subgroup of the automorphism group of the binary tree (`Garrido.BinaryTreeAut`), and let $g_1, g_2, \ldots$ be automorphisms such that, for every $n \ge 1$: $g_n \in \mathrm{St}_G(\mathsf L_n)$ (`levelStab G n`); and for every vertex $v$ of level $n$ and each digit $j$, the section $(g_n)_v$ (`sec`) moves the vertex $j$ of level 1, that is, the root permutation of $(g_n)_v$ has no fixed point. Then $(g_n)$ has the cube independence property on the orbit $1^\infty \cdot G$ (`IsCubeIndependent` with parameters $k_n = 1$): for every $n \ge 1$ and every $x \in 1^\infty \cdot G$, the $2^n$ rays $x \cdot g_n^{\varepsilon_n} \cdots g_1^{\varepsilon_1}$, $(\varepsilon_1, \ldots, \varepsilon_n) \in \{0, 1\}^n$, are distinct.
--
--   Erschler and Zheng, p. 27, Lemma 5.6: “Let $G < \mathrm{Aut}(\mathsf T_d)$ and suppose that $g_n \in G$ satisfies that $g_n \in \mathrm{St}_G(\mathsf L_n)$ and the root permutation of the section $(g_n)_v$ has no fixed point for all $v \in \mathsf L_n$. Then the sequence $(g_n)_{n \geqslant 0}$ has the cube independence property on $1^\infty \cdot G$.”
--
--   This is the lemma for the binary tree, $d_j = 2$ for every $j$, the case §7 applies to the elements (7.1) of $G_\omega$; the general statement is [`ErschlerZheng.isCubeIndependent_of_mem_levelStab_of_rootPerm_ne`](https://prove2.me/theorems/8c49f339-ea0c-4914-8b44-9ca664b072bd). As there, the sequence is indexed from $1$ and $g_0$ plays no role.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 27, Lemma 5.6, for the binary tree

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
open scoped RightActions

namespace ErschlerZheng

theorem isCubeIndependent_of_mem_levelStab_of_sec_smul_ne (G : Subgroup Garrido.BinaryTreeAut)
    (g : ℕ → Garrido.BinaryTreeAut) (hg : ∀ n, 1 ≤ n → g n ∈ levelStab G n)
    (hroot : ∀ n, 1 ≤ n → ∀ v : List Bool, v.length = n → ∀ j : Bool, [j] <• sec (g n) v ≠ [j]) :
    IsCubeIndependent (rightOrbit G oneRay) (fun _ => 1) g := by
  sorry

end ErschlerZheng
