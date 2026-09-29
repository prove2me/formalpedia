-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
-- name    : CerednikDrinfeld.SpecialFormalODModule.forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/5c7b246d-8974-5c99-bd70-1083cbb5b31b
-- title:
--   A critical index exists: λ(varpi) kills one eigenline
-- statement:
--   Let $q$ be a prime, let $k$ be a field of characteristic $q$, and let $j\colon W(\mathbb F_{q^2}) \to k$ be a ring homomorphism, where `Zp2 q` denotes the Witt vectors of the field `GaloisField q 2` with $q^2$ elements. Let $X_0$ be a `SpecialFormalODModule q j`, that is: a $2$-dimensional formal group law $F$ over $k$ (given by two power series in two pairs of variables satisfying the normalisation, associativity and commutativity conditions), together with series $\mathrm{act}(a)$ for $a \in W(\mathbb F_{q^2})$ and a series $\varpi$, all endomorphisms of the law, such that $\mathrm{act}(1)$ is the identity, $\mathrm{act}(ab) = \mathrm{act}(a)\circ\mathrm{act}(b)$, $\mathrm{act}(a+b)$ is the sum of $\mathrm{act}(a)$ and $\mathrm{act}(b)$ via $F$, $\varpi\circ\varpi = \mathrm{act}(q)$ and $\varpi\circ\mathrm{act}(a) = \mathrm{act}(\mathrm{Frob}\,a)\circ\varpi$; subject moreover to `isSpecial` (the submodules $\mathrm{Lie}_0 = \bigcap_a \ker(\lambda(\mathrm{act}(a)) - j(a))$ and $\mathrm{Lie}_1 = \bigcap_a \ker(\lambda(\mathrm{act}(a)) - j(\mathrm{Frob}\,a))$ of the Lie module are complementary and both invertible) and to `hasHeight 4` (the kernel of $\mathrm{act}(q)$ has degree $q^4$). Here $\lambda(\phi)$ is the matrix of coefficients of the linear terms of a tuple of series. The conclusion is that the endomorphism $m \mapsto \lambda(\varpi)\,m$ of the Lie module vanishes on all of $\mathrm{Lie}_0$, or else vanishes on all of $\mathrm{Lie}_1$.
--
--   In Drinfeld's description of special formal $\mathcal O_D$-modules over a field of characteristic $q$, an index $i$ with $\lambda(\varpi)|_{\mathrm{Lie}_i} = 0$ is called a critical index; the statement asserts that at least one critical index exists (both occur exactly at the double points of the reduction). It is used in the analysis of special formal $\mathcal O_D$-modules arising as Witt-vector quotients, in [`CerednikDrinfeld.FormalODModule.lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient`](thm.html#CerednikDrinfeld.FormalODModule.lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
    {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [CharP k q]
    (j : Zp2 q →+* k) (X₀ : SpecialFormalODModule q j) :
    (∀ m ∈ X₀.toFormalODModule.lieZero j, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∨
      (∀ m ∈ X₀.toFormalODModule.lieOne j, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) := by sorry
