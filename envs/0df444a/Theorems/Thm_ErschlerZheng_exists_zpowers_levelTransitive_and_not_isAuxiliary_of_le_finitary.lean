-- Prove2me | Theorems.Thm_ErschlerZheng_exists_zpowers_levelTransitive_and_not_isAuxiliary_of_le_finitary
-- name    : ErschlerZheng.exists_zpowers_levelTransitive_and_not_isAuxiliary_of_le_finitary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:29.431505+00:00
-- url     : https://prove2.me/theorems/3d543104-dcca-4724-b3b6-d60c47de1acf
-- title:
--   p. 18, as printed, fails — for the level-transitive binary odometer, no group of finitary automorphisms is an auxiliary group
-- statement:
--   There is an automorphism $\tau$ of the binary tree (`Garrido.BinaryTreeAut`) whose cyclic group $G = \langle \tau \rangle$ (`Subgroup.zpowers`) acts transitively on every level — for any two vertices $u, v$ of the same length some $g \in G$ has $u \cdot g = v$ — such that no subgroup $K$ of the group $L$ of finitary automorphisms (`finitary`) is an auxiliary group with trivial isotropy for $G$ acting on the rays (`IsAuxiliary`).
--
--   Erschler and Zheng, p. 18: “For $G < \mathrm{Aut}(\mathsf T_{\mathbf d})$, we use the group $L_G = \{\gamma \in L : x \cdot \gamma \in x \cdot G \text{ for all } x \in \partial \mathsf T\}$ as an auxiliary group with trivial isotropy groups. In particular if $G$ acts level transitively, then $L$ is used as the auxiliary group.”
--
--   The statement refutes both sentences as printed for a general $G$: for this $G$, which acts level transitively, neither $L_G \le L$ nor $L$ itself is an auxiliary group. The paragraph prepares the examples that follow (“We now discuss some examples of groupoid of germs of groups acting on rooted trees”), and the paper applies it only to the Grigorchuk groups $G_\omega$ (Example 3.2), where it holds: that is the milestone `ErschlerZheng.isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 18, the finitary group L for a general G, as printed (fails for the odometer)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

open scoped RightActions

namespace ErschlerZheng

theorem exists_zpowers_levelTransitive_and_not_isAuxiliary_of_le_finitary :
    ∃ τ : Garrido.BinaryTreeAut,
      (∀ u v : List Bool, u.length = v.length → ∃ g ∈ Subgroup.zpowers τ, u <• g = v) ∧
      ∀ K : Subgroup Garrido.BinaryTreeAut, K ≤ finitary →
        ¬ IsAuxiliary (X := Ray) (Subgroup.zpowers τ) K := by
  sorry

end ErschlerZheng
