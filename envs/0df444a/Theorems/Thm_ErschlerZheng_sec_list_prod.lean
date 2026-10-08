-- Prove2me | Theorems.Thm_ErschlerZheng_sec_list_prod
-- name    : ErschlerZheng.sec_list_prod
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T00:32:21.561126+00:00
-- url     : https://prove2.me/theorems/4264bece-23fb-471c-8b1c-fe17162bc8fd
-- title:
--   (7.17) — the section of a product at z is the product of the sections at the successive images of z
-- statement:
--   For any finite list $g_1, \ldots, g_m$ of automorphisms of the binary tree (`Garrido.BinaryTreeAut`) and any vertex $z$,
--   $$(g_1 g_2 \cdots g_m)_z = (g_1)_z\, (g_2)_{z \cdot g_1}\, (g_3)_{z \cdot g_1 g_2} \cdots (g_m)_{z \cdot g_1 \cdots g_{m-1}},$$
--   where $h_v$ is the section of $h$ at $v$ for the right action (`sec`: $(vy) \cdot h = (v \cdot h)(y \cdot h_v)$). The list may be empty, in which case both sides are the identity, and the automorphisms are arbitrary.
--
--   Erschler and Zheng, p. 54: “To see this, denote by $z$ the length $n + D + 1$ prefix of $x$, $z = x_1 \ldots x_{n+D+1}$, and consider the section at $z$: (7.17) $\bigl(\gamma_{j+1}^{-\epsilon_{j+1}} \ldots \gamma_m^{-\epsilon_m}\bigr)_z = \bigl(\gamma_{j+1}^{-\epsilon_{j+1}}\bigr)_z \bigl(\gamma_{j+2}^{-\epsilon_{j+2}}\bigr)_{z \cdot \gamma_{j+1}^{-\epsilon_{j+1}}} \ldots \bigl(\gamma_m^{-\epsilon_m}\bigr)_{z \cdot \gamma_{j+1}^{-\epsilon_{j+1}} \ldots \gamma_{m-1}^{-\epsilon_{m-1}}}$.”
--
--   The paper writes (7.17) for one product in the proof of Lemma 7.21 and uses the same rule throughout without comment; the statement is the rule for an arbitrary product.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 54, (7.17)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
open scoped RightActions

namespace ErschlerZheng

theorem sec_list_prod (l : List Garrido.BinaryTreeAut) (z : List Bool) :
    sec l.prod z = (List.ofFn fun i : Fin l.length => sec l[i] (z <• (l.take i).prod)).prod := by
  sorry

end ErschlerZheng
