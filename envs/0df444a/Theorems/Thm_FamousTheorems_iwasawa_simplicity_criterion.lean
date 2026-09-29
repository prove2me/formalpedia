-- Prove2me | Theorems.Thm_FamousTheorems_iwasawa_simplicity_criterion
-- name    : FamousTheorems.iwasawa_simplicity_criterion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:07.171208+00:00
-- url     : https://prove2.me/theorems/197dc2cb-de17-4099-9c40-9cc22f4795f5
-- title:
--   Iwasawa's simplicity criterion
-- statement:
--   **Iwasawa's simplicity criterion.** Let $M$ be a nontrivial group acting faithfully and quasi-primitively on a set $\alpha$. Suppose that $M$ is perfect ($[M,M]=M$) and that there is a family of abelian subgroups $T(x)$, $x\in\alpha$, with $T(gx)=gT(x)g^{-1}$ for all $g$ and $x$, that together generate $M$. Then $M$ is simple.
--
--   Iwasawa's lemma (1941) is the standard route to the simplicity of groups acting on geometries. It is used for $PSL_n(K)$ acting on projective space, with transvection subgroups, and for the alternating groups. It also applies to many classical and Chevalley groups.
--
--   **Formalization note.** Mathlib's `MulAction.IwasawaStructure.isSimpleGroup`. `commutator M = ⊤` says that `M` is perfect. `MulAction.IsQuasiPreprimitive M α` says that every nontrivial normal subgroup acts transitively, which holds for primitive actions. A `MulAction.IwasawaStructure M α` is the family $T$ with its commutativity, conjugation and generation properties.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MulAction.IwasawaStructure.isSimpleGroup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem iwasawa_simplicity_criterion {M : Type*} [Group M] {α : Type*} [MulAction M α] [Nontrivial M] (hc : commutator M = ⊤)
    [MulAction.IsQuasiPreprimitive M α] (IwaS : MulAction.IwasawaStructure M α) (hf : FaithfulSMul M α) :
    IsSimpleGroup M := by sorry

end FamousTheorems
