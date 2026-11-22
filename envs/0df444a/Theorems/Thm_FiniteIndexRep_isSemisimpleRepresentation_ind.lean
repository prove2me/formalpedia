-- Prove2me | Theorems.Thm_FiniteIndexRep_isSemisimpleRepresentation_ind
-- name    : FiniteIndexRep.isSemisimpleRepresentation_ind
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:00.788776+00:00
-- url     : https://prove2.me/theorems/a3aeb698-263a-4e0b-8fcb-5f6ac0842402
-- title:
--   Induction from a subgroup of finite index preserves semisimplicity of finite-dimensional representations in characteristic $0$
-- statement:
--   **Induction from a subgroup of finite index preserves semisimplicity.** Let $k$ be a field of characteristic $0$, let $G$ be a group and $H\le G$ a subgroup of finite index, and let $\sigma\colon H\to\mathrm{GL}(V)$ be a semisimple representation of $H$ on a finite-dimensional $k$-vector space $V$. The induced representation is
--   $$\mathrm{Ind}_H^G(\sigma)=k[G]\otimes_{k[H]}V,$$
--   with $G$ acting by left multiplication on the first factor. It has dimension $[G:H]\dim V$. Then
--   $$\mathrm{Ind}_H^G(\sigma)\ \text{is a semisimple representation of } G.$$
--
--   This is the group-theoretic content of Proposition 14.1.1.1(5)(b) of the source. There it is applied to $G=W_F$ a Weil group, $H=W_E$ the open subgroup of finite index attached to a finite separable extension $E/F$, and $\sigma$ the restriction to $W_E$ of an irreducible representation of $W_F$. This restriction is semisimple by the companion statement `FiniteIndexRep.isSemisimpleRepresentation_iff_comp_subtype`, and by Clifford's theorem when $E/F$ is Galois, so that $W_E$ is normal. In the proof of Proposition 14.1.2.3 the source uses it to decompose $\mathrm{Ind}_{W_{F'/F}}^{W_{F'/\mathbb Q}}(\chi')$ into irreducible constituents. There the induced object is a character $\chi'$ of the subgroup $W_{F'/F}$, a one-dimensional and hence semisimple representation, which the arbitrary semisimple $\sigma$ of the statement covers. With the additivity and inductivity of Artin–Weil $L$-functions, this gives the factorization $L(s,\chi)=\prod_\lambda L(s,\lambda)^{n_\lambda}$.
--
--   **Formalization Note.** The induced representation is Mathlib's `Representation.ind H.subtype σ`, defined as the coinvariants $(k[G]\otimes_k V)_H$. This is the induced representation, left adjoint to restriction (`Rep.indResAdjunction`). Semisimplicity is `Representation.IsSemisimpleRepresentation`. The source states the result for continuous complex representations of Weil groups. Here $G$ is an arbitrary group, $k$ any field of characteristic $0$, and $\sigma$ any semisimple finite-dimensional representation of $H$, not only the restriction of an irreducible representation of $G$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 525, Proposition 14.1.1.1(5)(b) (proof on p. 526), stated for an arbitrary group and subgroup of finite index

import Mathlib

set_option autoImplicit false

namespace FiniteIndexRep

/-- In characteristic zero, the representation induced from a semisimple finite-dimensional
representation of a subgroup `H` of finite index of `G` is a semisimple representation of `G`. -/
theorem isSemisimpleRepresentation_ind {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (H : Subgroup G) [H.FiniteIndex] (σ : Representation k H V)
    (hσ : Representation.IsSemisimpleRepresentation σ) :
    Representation.IsSemisimpleRepresentation (Representation.ind H.subtype σ) := by
  sorry

end FiniteIndexRep
