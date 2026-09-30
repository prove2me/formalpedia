-- Prove2me | Theorems.Thm_AlgEquiv_zpowers_toFixedFieldAlgEquiv_eq_top
-- name    : AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:31:26.702403+00:00
-- url     : https://prove2.me/theorems/08c8d926-ac25-46be-8b3c-90dd6af6d729
-- title:
--   A finite cyclic subgroup generates the Galois group over its fixed field
-- statement:
--   Let $M/K$ be a field extension and $\sigma\in\operatorname{Aut}_K(M)$. Assume the cyclic subgroup $\langle\sigma\rangle$ is finite, and let $F=M^{\langle\sigma\rangle}$ be its fixed field. Regarding $\sigma$ as an $F$-automorphism,
--
--   $$
--   \operatorname{Aut}_F(M)=\langle\sigma\rangle.
--   $$
--
--   The cyclic fixed-field extension thus has the specified automorphism as a generator; no finiteness or Galois assumption on $M/K$ is imposed.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/FieldTheory/Galois/FixedField.lean#L444-L468), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/FieldTheory/Galois/FixedField.lean#L444-L468

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Fixed fields and fixing subgroups

Complements to Mathlib's Galois correspondence: its interaction with the complete-lattice
operations, when a fixed field and an intermediate field generate the whole extension, when the
correspondence survives dropping finiteness of `M / K` for a finite subgroup, and what the
correspondence gives for a cyclic subgroup.

Taking fixed fields always sends joins of automorphism subgroups to intersections of intermediate
fields. For a finite Galois extension it also sends subgroup intersections to composita of fixed
fields. Both the binary and indexed forms are recorded so that finite generating families and
arbitrary families can use these lattice laws without manually passing through the order dual in
the Galois correspondence.

For a finite Galois extension `M / K`, a subgroup `H ≤ Gal(M/K)` and an intermediate field `E`,
the fixed field of `H` and `E` generate `M` exactly when `H` meets the fixers of `E` trivially.
With no hypothesis on `M / K`, the fixers of an arbitrary join of intermediate fields are the
automorphisms fixing each of them.

The correspondence is equivariant for conjugation: the fixed field of a conjugate subgroup is the
image of the fixed field under the conjugating automorphism.

The correspondence between subgroups and their fixed fields also holds with no hypothesis on
`M / K` at all, provided the subgroup is finite: Artin's theorem makes `M` finite Galois over the
fixed field of a finite `H`, and the fixers of that field are then exactly `H`. This is how a
subgroup of the automorphism group of an infinite extension is recovered from the field it cuts
out; the fixing subgroup of a subfield of finite degree is finite for the same reason.

The last results specialise the correspondence to a *cyclic* subgroup: the field fixed by a finite
cyclic group of automorphisms has `M` cyclic over it, and for `⟨σ⟩` there is a named automorphism
over the fixed field — `AlgEquiv.toFixedFieldAlgEquiv σ` acts on `M` as `σ` does, and generates
once `⟨σ⟩` is finite.

Neither `M / K` Galois nor `M / K` finite is needed, and neither is faithfulness of the action:
`FixedPoints.toAlgAut_surjective` asks only that the group be finite, and cyclicity passes along
its surjection. The fixed-point subfield it produces is the one underlying
`IntermediateField.fixedField`.

A simple extension `K⟮x⟯` is fixed pointwise by exactly those automorphisms that fix `x`, so
its fixing subgroup is the stabilizer of `x`; this too needs no hypothesis on `M / K` at all.

Two facts hold for every intermediate field `E` algebraic over `K`, with no separability anywhere
and nothing asked of `M / K`: its fixing subgroup is closed in the Krull topology, being the
intersection over the finite simple subextensions of their open fixing subgroups; and it is
unchanged by cutting `E` down to its part inside `separableClosure K M`, because every element of
`E` has a `q`-th power iterate there. The second is why a Galois correspondence over an
inseparable extension can only be indexed by the intermediate fields of the separable closure.

## Main results

* `Subgroup.fixedField_inf` and `Subgroup.fixedField_sup`
* `Subgroup.fixedField_iInf` and `Subgroup.fixedField_iSup`
* `Subgroup.fixedField_sup_eq_top_iff`
* `Subgroup.fixedField_map_conj`
* `IntermediateField.fixingSubgroup_inf`
* `IntermediateField.fixingSubgroup_iSup`
* `IntermediateField.fixingSubgroup_isClosed_of_isAlgebraic`
* `IntermediateField.fixingSubgroup_inf_separableClosure`
* `IntermediateField.fixingSubgroup_fixedField_of_finite`
* `IntermediateField.finite_of_finiteDimensional_fixedField`
* `IntermediateField.card_fixingSubgroup_le`
* `IntermediateField.fixingSubgroup_adjoin_simple`, with
  `IntermediateField.mem_fixedField_stabilizer`,
  `IntermediateField.fixedField_stabilizer_eq_adjoin_simple`,
  `IntermediateField.fixedField_iInf_stabilizer_eq_adjoin_range` and
  `IntermediateField.adjoin_eq_top_of_fixedField_stabilizer`: the stabilizer of `x` fixes
  exactly `K⟮x⟯`, in which `x` is a primitive element
* `FixedPoints.isCyclic_algEquiv`
* `AlgEquiv.toFixedFieldAlgEquiv`, with `AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top` and
  `AlgEquiv.card_algEquiv_fixedField_zpowers`
* `TauCeti.natCard_algEquiv_dvd_finrank`: the automorphism group of a finite extension has order
  dividing the degree, since that order is the degree over the field fixed by all automorphisms
-/

 section

open IntermediateField

namespace IntermediateField
end IntermediateField
section IntermediateField
open IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]







end IntermediateField

namespace Subgroup
end Subgroup
section Subgroup
open Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]











end Subgroup

namespace IntermediateField
end IntermediateField
section IntermediateField
open IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

















-- The subgroup extensionality argument below, reducing membership of `K⟮x⟯.fixingSubgroup` to
-- `IntermediateField.forall_mem_adjoin_smul_eq_self_iff` at the singleton `{x}`, is adapted from
-- the proof of `stabilizer_isOpen_of_isIntegral` in `Mathlib/FieldTheory/KrullTopology.lean`,
-- which uses it there to identify a point stabilizer with the fixing subgroup of a finite
-- intermediate field. Here it is recorded as a statement in its own right, with no integrality
-- hypothesis.










end IntermediateField

namespace Subgroup
end Subgroup
section Subgroup
open Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]



end Subgroup

namespace FixedPoints
end FixedPoints
section FixedPoints
open FixedPoints



end FixedPoints

namespace AlgEquiv
end AlgEquiv
section AlgEquiv
open AlgEquiv

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

-- Source. The fixed field of `⟨σ⟩` and its named generator are the constructions pinned at
-- `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 283-291, as `cyclicFixedField` and
-- `fixedFieldGenerator`. Neither name is kept: the field is spelled
-- `IntermediateField.fixedField (Subgroup.zpowers σ)` throughout rather than abbreviated, and the
-- automorphism is `toFixedFieldAlgEquiv`, because it is defined without finiteness and only
-- generates once `⟨σ⟩` is finite.

@[simp]
theorem AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top (σ : M ≃ₐ[K] M) [_root_.Finite (_root_.Subgroup.zpowers σ)] :
    _root_.Subgroup.zpowers (_root_.AlgEquiv.toFixedFieldAlgEquiv σ) = ⊤ := by sorry
