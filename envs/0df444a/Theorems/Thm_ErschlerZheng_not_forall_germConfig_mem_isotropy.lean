-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_germConfig_mem_isotropy
-- name    : ErschlerZheng.not_forall_germConfig_mem_isotropy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:12.260291+00:00
-- url     : https://prove2.me/theorems/3e371f7c-7f6c-4dd3-9bc9-a315888dd4aa
-- title:
--   Fact 3.5, (3.3) as printed, fails — the germ configuration Φ_g(x) need not lie in 𝒢_x
-- statement:
--   It is not true that for all subgroups $G$ and $L$ of the automorphism group of the binary tree, acting on the boundary $\partial\mathsf T$ (`Ray`) from the right, such that $L$ is an auxiliary group with trivial isotropy for $G$ (`IsAuxiliary`), every $g \in G$ and every point $x$ of the orbit $1^\infty \cdot G$ (`rightOrbit … oneRay`) satisfy $\Phi_g(x) \in \mathcal G_x$, where $\Phi_g(x)$ is the germ configuration (`germConfig L g x`) and $\mathcal G_x$ the isotropy group of $G$ at $x$ (`isotropy G x`).
--
--   Erschler and Zheng, p. 19, Fact 3.5 and (3.3): “Let $\vartheta : G \to \mathcal W$ by defined as $\vartheta(g) = (\Phi_g, g)$ such that for $x \in o \cdot G$, $\Phi_g(x) = (g\sigma^{-1}, x) \in \mathcal G_x$, where $\sigma \in L$, $x \cdot g = x \cdot \sigma$.”
--
--   The statement is the negation of the membership in $\mathcal G_x$ as printed, in the setting of the binary tree and with $o = 1^\infty$. The group $\mathcal W = (\prod_{x \in o \cdot G} \hat{\mathcal G}_x) \rtimes G$ of p. 19 takes its factors in $\hat{\mathcal G}_x$, the isotropy group of $\langle G, L \rangle$; the corrected membership, $\Phi_g(x) \in \hat{\mathcal G}_x$, is the first conjunct of the milestone `ErschlerZheng.germConfig_mul_and_injective`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 19, Fact 3.5, (3.3) as printed (fails)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

open scoped RightActions

namespace ErschlerZheng

theorem not_forall_germConfig_mem_isotropy :
    ¬ ∀ G L : Subgroup Garrido.BinaryTreeAut, IsAuxiliary (X := Ray) G L →
      ∀ g ∈ G, ∀ x ∈ rightOrbit (X := Ray) G oneRay, germConfig L g x ∈ isotropy G x := by
  sorry

end ErschlerZheng
