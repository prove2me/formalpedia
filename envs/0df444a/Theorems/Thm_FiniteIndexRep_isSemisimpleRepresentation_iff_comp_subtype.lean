-- Prove2me | Theorems.Thm_FiniteIndexRep_isSemisimpleRepresentation_iff_comp_subtype
-- name    : FiniteIndexRep.isSemisimpleRepresentation_iff_comp_subtype
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:00.388556+00:00
-- url     : https://prove2.me/theorems/9fc51ea8-65c1-40d1-89c3-b2773792b5e5
-- title:
--   Semisimplicity of a finite-dimensional representation in characteristic $0$ is detected on any subgroup of finite index
-- statement:
--   **Semisimplicity is detected on a subgroup of finite index.** Let $k$ be a field of characteristic $0$, let $G$ be a group and $H\le G$ a subgroup of finite index $[G:H]<\infty$, and let $\rho\colon G\to\mathrm{GL}(V)$ be a representation of $G$ on a finite-dimensional $k$-vector space $V$. Recall that $\rho$ is *semisimple* (completely reducible) if every $G$-stable subspace of $V$ admits a $G$-stable complement; $\rho|_H$ denotes the restriction of $\rho$ to $H$. Then
--   $$\rho\ \text{is semisimple}\iff\rho|_H\ \text{is semisimple}.$$
--
--   The implication "$\Leftarrow$" is the relative form of Maschke's theorem. When $H$ is normal, "$\Rightarrow$" is Clifford's theorem, which holds in every characteristic. For an arbitrary subgroup of finite index, "$\Rightarrow$" can fail in positive characteristic, so it needs characteristic $0$ (see the Formalization Note). In §14.1.1 of the source this is the reason why a finite-dimensional complex representation of the local Weil group $W_{E_v/F_{v_0}}$ on which every element acts semisimply is semisimple: its restriction to the abelian normal subgroup of finite index $E_v^\times$ is semisimple (p. 526). It is also used in the proof of Proposition 14.1.1.1(5)(b), to pass between a representation of $W_F$ and its restriction to the open subgroup of finite index $W_E$. The statement applies to Weil groups, profinite and arithmetic groups, and more generally to any group with a subgroup of finite index.
--
--   **Formalization Note.** A representation is a monoid homomorphism `ρ : Representation k G V` (that is, $G\to\mathrm{End}_k(V)$), its restriction to $H$ is `ρ.comp H.subtype`, and semisimplicity is Mathlib's `Representation.IsSemisimpleRepresentation` (every subrepresentation has a complement). The source works with continuous representations of topological groups over $\mathbb C$. Continuity plays no role, because semisimplicity only involves the invariant subspaces. The statement is given over any field of characteristic $0$. The hypothesis on the characteristic cannot be dropped: "$\Leftarrow$" fails when the characteristic divides $[G:H]$, and "$\Rightarrow$" can fail for non-normal $H$ in positive characteristic.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 526, the paragraph beginning "Since $E_v^\times\subset W_{E_v/F_{v_0}}$ is a normal subgroup of finite index" (a representation of $W_{E_v/F_{v_0}}$ on which every element acts semisimply is semisimple, because $E_v^\times$ is a normal subgroup of finite index), and proof of Proposition 14.1.1.1(5)(b); classical reference: R. P. Langlands, On the Functional Equation of the Artin L-Functions, unpublished preprint, 1970, Ch. 1, Lemma 1.1, p. 5 (as cited by the paper at the end of the next paragraph, p. 526)

import Mathlib

set_option autoImplicit false

namespace FiniteIndexRep

/-- In characteristic zero, a finite-dimensional representation of a group `G` is semisimple if and
only if its restriction to a subgroup `H` of finite index is semisimple. -/
theorem isSemisimpleRepresentation_iff_comp_subtype {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) (H : Subgroup G) [H.FiniteIndex] :
    Representation.IsSemisimpleRepresentation ρ ↔
      Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) := by
  sorry

end FiniteIndexRep
